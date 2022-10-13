//! Parses an R1CS file
//! File format specification found here: https://github.com/iden3/r1csfile/blob/master/doc/r1cs_bin_format.md

use std::io::{Read, Result};

use byteorder::{LittleEndian, ReadBytesExt};
use num_bigint::BigUint;

/// A type that implements readable is readable before a header has been found
trait Readable {
    /// The output type, for maximum flexibility this is not necessarily Self
    type Output;

    /// Read self from byte buffer
    fn read<R: Read>(r: &mut R) -> Result<Self::Output>;
}

/// A type that implements ReadableWithHeader is readable after the header has
/// been parsed from the file
trait ReadableWithHeader {
    /// The output type, for maximum flexibility this is not necessarily Self
    type Output;

    /// Read self from byte buffer
    fn read<R: Read>(header: &HeaderSection, r: &mut R) -> Result<Self::Output>;
}

/// Represents metadata about the file that occurs once in the prelude
#[derive(Debug, Clone, PartialEq, Eq)]
struct Metadata {
    /// The parsed magic number, should be equal to `MAGIC`
    _magic: u32,
    /// The parsed version number, should be 1 for our purposes
    version: u32,
    /// The number of sections
    num_sections: u32,
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
#[derive(Debug, Clone, PartialEq, Eq)]
enum SectionType {
    Header,
    Constraints,
    WireMap,
    CustomGateList,        // Not supported by the library
    CustomGateApplication, // Not supported by the library
    Undefined,             // Specification suggests we ignore undefined secitons for forward compat
}

/// Convert via enum indexing
impl<T: Into<u64>> From<T> for SectionType {
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

impl Readable for SectionType {
    type Output = Self;

    fn read<R: Read>(r: &mut R) -> Result<Self::Output> {
        // 4 bytes for section type
        Ok(Self::from(r.read_u32::<LittleEndian>()? as u64))
    }
}

/// Represents a section header, type + size
#[derive(Debug, Clone, PartialEq, Eq)]
struct SectionHeader {
    type_: SectionType,
    size: u64,
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
struct HeaderSection {
    /// The number of bytes allocated to field elements
    /// should be multiple of 8
    field_size: u32,
    /// The prime modulus of the constraint system's field
    field_prime: BigUint,
    /// The number of wires in the circuit
    num_wires: u32,
    /// The number of public outputs in the circuit
    num_public_outputs: u32,
    /// The number of public inputs in the circuit
    num_public_inputs: u32,
    /// The number of private inputs in the circuit
    num_private_inputs: u32,
    /// The number of labels in the circuit
    /// Labels include public/private inputs and intermediate values
    num_labels: u64,
    /// The total number of constraints in the system
    num_constraints: u32,
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
struct Constraints {
    constraints: Vec<SingletonConstraint>,
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
struct SingletonConstraint {
    // The elements of the `A` linear combination
    a_lc: Vec<(u32, BigUint)>,
    // The elements of the `B` linear combination
    b_lc: Vec<(u32, BigUint)>,
    // The elements of the `C` linear combination
    c_lc: Vec<(u32, BigUint)>,
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
struct LinearCombination {}

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
struct WireIdLabelMap {
    /// The mapping from wires (index) to label id (value)
    wire_map: Vec<u64>,
}

impl ReadableWithHeader for WireIdLabelMap {
    type Output = Self;

    fn read<R: Read>(header: &HeaderSection, r: &mut R) -> Result<Self::Output> {
        let mut wire_map = Vec::with_capacity(header.num_wires as usize);
        for _ in 0..header.num_wires {
            wire_map.push(r.read_u64::<LittleEndian>()?);
        }

        Ok(Self { wire_map })
    }
}

/// Represents a single field element in the circuit
#[derive(Debug, Clone, PartialEq, Eq)]
struct FieldElement {
    value: BigUint,
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

#[cfg(test)]
mod test {
    use std::{fs::File, io::Read};

    use crate::parser::{HeaderSection, Metadata};

    use super::{Readable, SectionHeader, SectionType};

    const TEST_FILE: &str = "./resources/test.r1cs";

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
        let mut test_file = File::open(TEST_FILE).unwrap();
        // Read the metadata
        Metadata::read(&mut test_file).unwrap();

        let mut header = None;
        while let Ok(section) = SectionHeader::read(&mut test_file) {
            if section.type_ == SectionType::Header {
                header = Some(HeaderSection::read(&mut test_file).unwrap());
            } else {
                // Read through this section
                let mut buf = vec![0u8; section.size.try_into().unwrap()];
                test_file.read_exact(&mut buf).unwrap();
                continue;
            }
        }

        assert!(header.is_some());
        let header = header.unwrap();

        // Ground truth values determined by circom compiler output
        assert_eq!(header.num_public_inputs, 1);
        assert_eq!(header.num_private_inputs, 2);
        assert_eq!(header.num_public_outputs, 0);
        assert_eq!(header.num_constraints, 1);
        assert_eq!(header.num_labels, 4);
        assert_eq!(header.num_wires, 4);
        assert_eq!(header.field_size, 32);
    }
}
