//! Defines sections of an R1CS file and parsing logic for each
//! File format specification found here: https://github.com/iden3/r1csfile/blob/master/doc/r1cs_bin_format.md

use std::io::{Error, ErrorKind, Read, Result, Write};

use byteorder::{LittleEndian, ReadBytesExt};
use num_bigint::BigUint;

/// A type that implements readable is readable before a header has been found
pub(crate) trait Readable {
    /// The output type, for maximum flexibility this is not necessarily Self
    type Output;

    /// Read self from byte buffer
    fn read<R: Read>(r: &mut R) -> Result<Self::Output>;
}

/// A type that implements ReadableWithHeader is readable after the header has
/// been parsed from the file
pub(crate) trait ReadableWithHeader {
    /// The output type, for maximum flexibility this is not necessarily Self
    type Output;

    /// Read self from byte buffer
    fn read<R: Read>(header: &HeaderSection, r: &mut R) -> Result<Self::Output>;
}

/// Represents metadata about the file that occurs once in the prelude
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct Metadata {
    /// The parsed magic number, should be equal to `MAGIC`
    pub(crate) _magic: u32,
    /// The parsed version number, should be 1 for our purposes
    pub(crate) version: u32,
    /// The number of sections
    pub(crate) num_sections: u32,
}

impl Readable for Metadata {
    type Output = Self;

    fn read<R: Read>(r: &mut R) -> Result<Self::Output> {
        // 4 bytes for the file's magic number
        let magic = r.read_u32::<LittleEndian>()?;
        // assert_eq!(magic.to_le_bytes(), MAGIC);

        // 4 bytes for the version
        let version = r.read_u32::<LittleEndian>()?;

        // 4 bytes for the number of sections
        let num_sections = r.read_u32::<LittleEndian>()?;

        Ok(Self {
            _magic: magic,
            version,
            num_sections,
        })
    }
}

/// Represents the type of a section that is in a header
#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub(crate) enum SectionType {
    Header,
    Constraints,
    WireMap,
    CustomGateList,        // Not supported by the library
    CustomGateApplication, // Not supported by the library
    Undefined,             // Specification suggests we ignore undefined secitons for forward compat
}

/// Convert via enum indexing
impl<T: Into<u32>> From<T> for SectionType {
    fn from(input: T) -> Self {
        match input.into() {
            1 => Self::Header,
            2 => Self::Constraints,
            3 => Self::WireMap,
            4 => Self::CustomGateList,
            5 => Self::CustomGateApplication,
            _ => Self::Undefined,
        }
    }
}

/// Convert back to u64 for writing
impl TryInto<u32> for SectionType {
    type Error = Error;

    fn try_into(self) -> Result<u32> {
        match self {
            SectionType::Header => Ok(1),
            SectionType::Constraints => Ok(2),
            SectionType::WireMap => Ok(3),
            SectionType::CustomGateList => Ok(4),
            SectionType::CustomGateApplication => Ok(5),
            SectionType::Undefined => {
                Err(Error::new(ErrorKind::InvalidData, "undefined section type"))
            }
        }
    }
}

impl Readable for SectionType {
    type Output = Self;

    fn read<R: Read>(r: &mut R) -> Result<Self::Output> {
        // 4 bytes for section type
        Ok(Self::from(r.read_u32::<LittleEndian>()?))
    }
}

/// Represents a section header, type + size
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct SectionHeader {
    pub(crate) type_: SectionType,
    pub(crate) size: u64,
}

impl SectionHeader {
    pub(crate) fn write_to_buffer<W: Write>(&self, mut w: W) -> Result<usize> {
        // Buffer self as bytes
        let mut bytes_written = 0;
        bytes_written += w.write(&TryInto::<u32>::try_into(self.type_)?.to_le_bytes())?;
        bytes_written += w.write(&self.size.to_le_bytes())?;

        Ok(bytes_written)
    }
}

impl Readable for SectionHeader {
    type Output = Self;

    fn read<R: Read>(r: &mut R) -> Result<Self::Output> {
        // Read the section type
        let section_type = SectionType::read(r)?;
        // Section size is the word size of the underlying execution
        // For now, assume this is 8 byte (64bit)
        let size = r.read_u64::<LittleEndian>()?;

        Ok(Self {
            type_: section_type,
            size,
        })
    }
}

/// Represents a header section in the R1CS spec
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct HeaderSection {
    /// The number of bytes allocated to field elements
    /// should be multiple of 8
    pub(crate) field_size: u32,
    /// The prime modulus of the constraint system's field
    pub(crate) field_prime: BigUint,
    /// The number of wires in the circuit
    pub(crate) num_wires: u32,
    /// The number of public outputs in the circuit
    pub(crate) num_public_outputs: u32,
    /// The number of public inputs in the circuit
    pub(crate) num_public_inputs: u32,
    /// The number of private inputs in the circuit
    pub(crate) num_private_inputs: u32,
    /// The number of labels in the circuit
    /// Labels include public/private inputs and intermediate values
    pub(crate) num_labels: u64,
    /// The total number of constraints in the system
    pub(crate) num_constraints: u32,
}

impl Readable for HeaderSection {
    type Output = Self;

    fn read<R: Read>(r: &mut R) -> Result<Self::Output> {
        // 4 bytes for the field size (in bytes)
        let field_size = r.read_u32::<LittleEndian>()?;
        assert!(field_size % 8 == 0, "Field size should be a multiple of 8");

        // The prime of the field will be of size <field_size>
        let mut field_prime_bytes = vec![0u8; field_size as usize];
        r.read_exact(&mut field_prime_bytes)?;
        let field_prime = BigUint::from_bytes_le(&field_prime_bytes);

        // 4 bytes for the number of wires in the circuit
        let num_wires = r.read_u32::<LittleEndian>()?;

        // 4 bytes for the number of public outputs in the circuit
        let num_public_outputs = r.read_u32::<LittleEndian>()?;

        // 4 bytes for the number of putlic inputs in the circuit
        let num_public_inputs = r.read_u32::<LittleEndian>()?;

        // 4 bytes for the number of private inputs in the circuit
        let num_private_inputs = r.read_u32::<LittleEndian>()?;

        // 8 bytes for the number of labels
        let num_labels = r.read_u64::<LittleEndian>()?;

        // 4 bytes for the number of constraints
        let num_constraints = r.read_u32::<LittleEndian>()?;

        Ok(Self {
            field_size,
            field_prime,
            num_wires,
            num_public_outputs,
            num_public_inputs,
            num_private_inputs,
            num_labels,
            num_constraints,
        })
    }
}

/// Represents the constraints specification in an R1SC circuit
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct Constraints {
    pub(crate) constraints: Vec<SingletonConstraint>,
}

impl ReadableWithHeader for Constraints {
    type Output = Self;

    fn read<R: Read>(header: &HeaderSection, r: &mut R) -> Result<Self::Output> {
        // Read in the constraints
        let mut constraints = Vec::with_capacity(header.num_constraints as usize);
        for _ in 0..header.num_constraints {
            constraints.push(SingletonConstraint::read(header, r)?);
        }

        Ok(Self { constraints })
    }
}

/// Represents a single constraint in the R1CS circuit
///
/// In R1CS, constraints are of the form:
///     (\sum_{i=i}^n a_i * w_i) * (\sum_{i=1}^n b_i * w_i) - (\sum_{i=1}^n c_i * w_i) = 0
/// This structure directly represents the linear combinations that go into A, B, C
/// In the form of lists of tuples: (wireID, coeff), where coeff is a field element
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct SingletonConstraint {
    // The elements of the `A` linear combination
    pub(crate) a_lc: Vec<(u32, BigUint)>,
    // The elements of the `B` linear combination
    pub(crate) b_lc: Vec<(u32, BigUint)>,
    // The elements of the `C` linear combination
    pub(crate) c_lc: Vec<(u32, BigUint)>,
}

impl ReadableWithHeader for SingletonConstraint {
    type Output = Self;

    fn read<R: Read>(header: &HeaderSection, r: &mut R) -> Result<Self::Output> {
        // Read in the linear combination for `A`
        Ok(Self {
            a_lc: LinearCombination::read(header, r)?,
            b_lc: LinearCombination::read(header, r)?,
            c_lc: LinearCombination::read(header, r)?,
        })
    }
}

/// Represents a linear combination in an R1CS constraint
/// The return type is Vec<(u32, BigUint)> representing pairs of
/// (wireID, coefficient)
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct LinearCombination {}

impl ReadableWithHeader for LinearCombination {
    type Output = Vec<(u32, BigUint)>;

    fn read<R: Read>(header: &HeaderSection, r: &mut R) -> Result<Self::Output> {
        // 4 bytes for the number of terms
        let num_terms = r.read_u32::<LittleEndian>()?;

        // Read in all the a constraints
        let mut terms = Vec::with_capacity(num_terms as usize);
        for _ in 0..num_terms {
            // 4 bytes for the wireID
            let wire_id = r.read_u32::<LittleEndian>()?;
            // One field element for the coefficient
            let coeff = FieldElement::read(header, r)?;

            terms.push((wire_id, coeff))
        }

        Ok(terms)
    }
}

/// Represents the Wire ID to label map of the circuit
///
/// Each wireID is mapped to one label
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct WireIdLabelMap {
    /// The mapping from wires (index) to label id (value)
    pub(crate) mapping: Vec<u64>,
}

impl WireIdLabelMap {
    #[allow(dead_code)]
    pub(crate) fn get_label(&self, wire_id: usize) -> u64 {
        self.mapping[wire_id]
    }
}

impl ReadableWithHeader for WireIdLabelMap {
    type Output = Self;

    fn read<R: Read>(header: &HeaderSection, r: &mut R) -> Result<Self::Output> {
        let mut mapping = Vec::with_capacity(header.num_wires as usize);
        for _ in 0..header.num_wires {
            mapping.push(r.read_u64::<LittleEndian>()?);
        }

        Ok(Self { mapping })
    }
}

/// Represents a single field element in the circuit
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct FieldElement {
    pub(crate) value: BigUint,
}

impl ReadableWithHeader for FieldElement {
    type Output = BigUint;

    fn read<R: Read>(header: &HeaderSection, r: &mut R) -> Result<Self::Output> {
        // Input is of unknown size at compile time, buffer it
        let mut felt_buf = vec![0u8; header.field_size as usize];
        r.read_exact(&mut felt_buf)?;

        Ok(BigUint::from_bytes_le(&felt_buf))
    }
}

/// All tests here rely on the test.r1cs file which represents a cicruit with
/// two private inputs; `a` and `b`, and one public input `c`. The circuit
/// verifies that a * b == c
#[cfg(test)]
mod test {
    use std::{fs::File, io::Read};

    use num_bigint::BigUint;

    use super::{
        Constraints, HeaderSection, Metadata, Readable, ReadableWithHeader, SectionHeader,
        SectionType, WireIdLabelMap,
    };

    const TEST_FILE: &str = "./resources/test.r1cs";

    /**
     * Helpers
     */

    /// Helper to find and parse the header of an R1CS file for tests that need
    /// header information upfront
    fn find_and_parse_header(file_name: &str) -> HeaderSection {
        // Open the file, find the header section, and parse it
        let mut test_file = File::open(file_name).unwrap();
        find_section(SectionType::Header, &mut test_file);

        HeaderSection::read(&mut test_file).unwrap()
    }

    /// Scan the file cursor through the binary until the given section type is found
    fn find_section<R: Read>(section_type: SectionType, mut reader: R) {
        // First read the metadata prelude
        Metadata::read(&mut reader).unwrap();

        // Loop over sections until correct type is found
        let mut found = false;
        while let Ok(section) = SectionHeader::read(&mut reader) {
            // If the type matches the given section, stop reading and let the caller
            // read through the upcoming section
            if section.type_ == section_type {
                found = true;
                break;
            } else {
                // Otherwise, read through this section entirely
                let mut buf = vec![0u8; section.size.try_into().unwrap()];
                reader.read_exact(&mut buf).unwrap();
                continue;
            }
        }

        assert!(found, "find_section could not find: {:?}", section_type);
    }

    /**
     * Tests
     */

    #[test]
    fn test_parse_metadata() {
        // Read in the metadata
        let mut test_file = File::open(TEST_FILE).unwrap();
        let md = Metadata::read(&mut test_file).unwrap();

        assert_eq!(md._magic, u32::from_le_bytes(*b"r1cs"));
        assert_eq!(md.num_sections, 3);
        assert_eq!(md.version, 1);
    }

    #[test]
    fn test_parse_header() {
        // Defer directly to the header helper
        let header = find_and_parse_header(TEST_FILE);

        // Ground truth values determined by circom compiler output
        assert_eq!(header.num_public_inputs, 1);
        assert_eq!(header.num_private_inputs, 2);
        assert_eq!(header.num_public_outputs, 0);
        assert_eq!(header.num_constraints, 1);
        assert_eq!(header.num_labels, 4);
        assert_eq!(header.num_wires, 4);
        assert_eq!(header.field_size, 32);
    }

    #[test]
    fn test_parse_constraints() {
        // Parse the header directly
        let header = find_and_parse_header(TEST_FILE);

        // Re-open the file and seek to the constraint section
        let mut file = File::open(TEST_FILE).unwrap();
        find_section(SectionType::Constraints, &mut file);

        // Parse the constraint section of the file and verify contents
        let constraint_section = Constraints::read(&header, &mut file).unwrap();

        assert_eq!(constraint_section.constraints.len(), 1);
        let constraint = &constraint_section.constraints[0];
        assert_eq!(constraint.a_lc.len(), 1);
        assert_eq!(constraint.b_lc.len(), 1);
        assert_eq!(constraint.c_lc.len(), 1);

        // Verify that the constraint represents w_1 * w_2 - w_3 = 0
        // i.e. all coefficients are one and the wires are mapped correctly
        // Wire 0 is mapped to a constant `1`, so wiring effectively starts at index 1
        // Public values are wired before private, so wiring order is (c, a, b)
        assert_eq!(constraint.c_lc[0].0, 1);
        assert_eq!(constraint.a_lc[0].0, 2);
        assert_eq!(constraint.b_lc[0].0, 3);

        assert_eq!(constraint.a_lc[0].1, BigUint::from(1u64));
        assert_eq!(constraint.b_lc[0].1, BigUint::from(1u64));
        assert_eq!(constraint.c_lc[0].1, BigUint::from(1u64));
    }

    #[test]
    fn test_wire_label_map() {
        // Parse the header
        let header = find_and_parse_header(TEST_FILE);

        // Re-open the file and seek to the wire map section
        let mut file = File::open(TEST_FILE).unwrap();
        find_section(SectionType::WireMap, &mut file);

        // Parse the wire map section and verify its contents
        let wire_map = WireIdLabelMap::read(&header, &mut file).unwrap();

        assert_eq!(wire_map.mapping.len(), 4);
        assert_eq!(wire_map.get_label(0 /* wire_id */), 0);
        assert_eq!(wire_map.get_label(1), 1);
        assert_eq!(wire_map.get_label(2), 2);
        assert_eq!(wire_map.get_label(3), 3);
    }
}
