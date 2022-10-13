//! Parses an R1CS file into a well defined interface

use std::{
    fs::File,
    io::{Error, ErrorKind, Read, Result},
};

use super::sections::{
    Constraints, HeaderSection, Metadata, Readable, ReadableWithHeader, SectionHeader, SectionType,
    SingletonConstraint, WireIdLabelMap,
};

/// Represents a partially parsed R1CS file
#[derive(Debug, Clone, Default, PartialEq, Eq)]
struct PartialR1CSFile {
    header: Option<HeaderSection>,
    constraints: Option<Vec<SingletonConstraint>>,
    wire_map: Option<WireIdLabelMap>,
}

impl PartialR1CSFile {
    fn new() -> Self {
        Self::default()
    }

    /// Reads a header section
    fn read_header<R: Read>(&mut self, mut r: R) -> Result<()> {
        self.header = Some(HeaderSection::read(&mut r)?);
        Ok(())
    }

    fn read_sections<R: Read>(&mut self, mut r: R) -> Result<()> {
        while let Ok(section) = SectionHeader::read(&mut r) {
            self.read_section(section.type_, &mut r)?;
        }

        Ok(())
    }

    /// Reads a section from the data and fills in internal data structure
    fn read_section<R: Read>(&mut self, section_type: SectionType, mut r: R) -> Result<()> {
        if self.header.is_none() {
            return Err(Error::new(ErrorKind::NotFound, "header not yet read"));
        }

        match section_type {
            SectionType::Constraints => {
                self.constraints =
                    Some(Constraints::read(self.header.as_ref().unwrap(), &mut r)?.constraints);
                Ok(())
            }
            SectionType::WireMap => {
                self.wire_map = Some(WireIdLabelMap::read(self.header.as_ref().unwrap(), &mut r)?);
                Ok(())
            }
            _ => Err(Error::new(
                ErrorKind::Unsupported,
                "unsupported section type",
            )),
        }
    }
}

impl TryInto<R1CSFile> for PartialR1CSFile {
    type Error = Error;

    fn try_into(self) -> Result<R1CSFile> {
        Ok(R1CSFile {
            header: self
                .header
                .ok_or_else(|| Error::new(ErrorKind::InvalidData, "missing header section"))?,
            constraints: self
                .constraints
                .ok_or_else(|| Error::new(ErrorKind::InvalidData, "missing constraints section"))?,
            wire_map: self
                .wire_map
                .ok_or_else(|| Error::new(ErrorKind::InvalidData, "missing wire map section"))?,
        })
    }
}

/// Represents a parsed R1CS file
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct R1CSFile {
    /// The R1CS header, contains information about the dimensions of the
    /// circuit, number of public/private inputs, etc
    pub(crate) header: HeaderSection,
    /// The constraint specification that defines the statement realized by
    /// the underlying circuit.
    /// Constraints come in the form:
    ///     (\sum_{i=0}^n a_i * w_i) * (\sum_{i=0}^n b_i * w_i) - (\sum_{i=0}^n c_i * w_i)
    pub(crate) constraints: Vec<SingletonConstraint>,
    pub(crate) wire_map: WireIdLabelMap,
}

impl R1CSFile {
    /// Parse an r1cs file into the data structure defined above
    pub fn parse(file_name: &str) -> Result<R1CSFile> {
        // Begin with a partial parse result
        let mut partial_parse = PartialR1CSFile::new();
        let mut file = File::open(file_name)?;

        // First, read through the metadata at the beginnning of the file
        Metadata::read(&mut file)?;

        // First, find the header and buffer the rest
        let mut skipped_data: &[u8] = &Self::seek_to_header(&mut file)?;
        partial_parse.read_header(&mut file)?;

        // Read the sections that were skipped while seeking for the header
        partial_parse.read_sections(&mut skipped_data)?;

        // Read the sections in the file that remain after seeking to the header
        partial_parse.read_sections(&mut file)?;

        // Attempt to reformat into a full parse
        partial_parse.try_into()
    }

    /// Find the header in the file,
    ///
    /// Returns a tuple representing the number of skipped sections and the
    /// raw bytes in those sections
    fn seek_to_header<R: Read>(mut r: R) -> Result<Vec<u8>> {
        let mut found = false;
        let mut skipped_data = Vec::new();

        while let Ok(section) = SectionHeader::read(&mut r) {
            // If this section is the header section, break and return, otherwise buffer and continue
            if section.type_ == SectionType::Header {
                found = true;
                break;
            } else {
                // Buffer the section header that was just read through
                section.write_to_buffer(&mut skipped_data)?;
                // Read through this section's data
                let mut buf = vec![
                    0u8;
                    section.size.try_into().map_err(|_| Error::new(
                        ErrorKind::InvalidData,
                        "error converting to usize"
                    ))?
                ];
                r.read_exact(&mut buf)?;
                skipped_data.append(&mut buf);

                continue;
            }
        }

        if !found {
            return Err(Error::new(
                ErrorKind::InvalidData,
                "header section not found",
            ));
        }

        Ok(skipped_data)
    }
}

#[cfg(test)]
mod test {
    use num_bigint::BigUint;

    use super::R1CSFile;

    const TEST_FILE: &str = "./resources/test.r1cs";

    #[test]
    /// An end to end parser test
    fn test_parse_r1cs_simple() {
        let parsed_r1cs = R1CSFile::parse(TEST_FILE).unwrap();

        // A collection of the test cases defined in sections::test
        // Header
        assert_eq!(parsed_r1cs.header.num_constraints, 1);
        assert_eq!(parsed_r1cs.header.num_private_inputs, 2);
        assert_eq!(parsed_r1cs.header.num_public_inputs, 1);
        assert_eq!(parsed_r1cs.header.num_public_outputs, 0);
        assert_eq!(parsed_r1cs.header.num_labels, 4);
        assert_eq!(parsed_r1cs.header.num_wires, 4);
        assert_eq!(parsed_r1cs.header.field_size, 32);

        // Constraints
        assert_eq!(parsed_r1cs.constraints.len(), 1);
        let single_constraint = &parsed_r1cs.constraints[0];
        assert_eq!(single_constraint.a_lc.len(), 1);
        assert_eq!(single_constraint.b_lc.len(), 1);
        assert_eq!(single_constraint.c_lc.len(), 1);

        // Verify that the constraint represents w_1 * w_2 - w_3 = 0
        // i.e. all coefficients are one and the wires are mapped correctly
        // Wire 0 is mapped to a constant `1`, so wiring effectively starts at index 1
        // Public values are wired before private, so wiring order is (c, a, b)
        assert_eq!(single_constraint.c_lc[0].0, 1);
        assert_eq!(single_constraint.a_lc[0].0, 2);
        assert_eq!(single_constraint.b_lc[0].0, 3);

        assert_eq!(single_constraint.a_lc[0].1, BigUint::from(1u64));
        assert_eq!(single_constraint.b_lc[0].1, BigUint::from(1u64));
        assert_eq!(single_constraint.c_lc[0].1, BigUint::from(1u64));

        // Wire map
        assert_eq!(parsed_r1cs.wire_map.mapping.len(), 4);
        assert_eq!(parsed_r1cs.wire_map.get_label(0 /* wire_id */), 0);
        assert_eq!(parsed_r1cs.wire_map.get_label(1), 1);
        assert_eq!(parsed_r1cs.wire_map.get_label(2), 2);
        assert_eq!(parsed_r1cs.wire_map.get_label(3), 3);
    }
}
