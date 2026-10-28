import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpFlatAdd

namespace OAI.Algorithms

/-! Reconstruct typed four-word coefficients from their existing raw bytes.
This is a representation bridge: no canonical-residue assumption is made,
and no additional machine execution is claimed. -/

namespace SubexponentialSAT.SubexpRawQuartic

open SubexpLiftRing SubexpQuarticRing

/-- Split a valid four-word payload at the three fixed word boundaries. -/
def split (B : ℕ) (bits : List Bool) (hbits : bits.length = 4 * B) : Quad (Word B) :=
  ⟨⟨bits.take B, by simp only [List.length_take]; omega⟩,
   ⟨(bits.drop B).take B, by simp only [List.length_take, List.length_drop]; omega⟩,
   ⟨((bits.drop B).drop B).take B, by
      simp only [List.length_take, List.length_drop]; omega⟩,
   ⟨((bits.drop B).drop B).drop B, by simp only [List.length_drop]; omega⟩⟩

@[simp] theorem encode_split (B : ℕ) (bits : List Bool) (hbits : bits.length = 4 * B) :
    SubexpFlatAdd.encode (split B bits hbits) = bits := by
  change bits.take B ++ ((bits.drop B).take B ++
    (((bits.drop B).drop B).take B ++ (((bits.drop B).drop B).drop B ++ []))) = bits
  simp only [List.append_nil, List.take_append_drop]

def zeroWord (B : ℕ) : Word B := ⟨List.replicate B false, by simp⟩

/-- A total local decoder. Valid payloads retain every input bit. -/
def ofBits (B : ℕ) (bits : List Bool) : Quad (Word B) :=
  if hbits : bits.length = 4 * B then split B bits hbits
  else ⟨zeroWord B, zeroWord B, zeroWord B, zeroWord B⟩

theorem encode_ofBits (B : ℕ) (bits : List Bool) (hbits : bits.length = 4 * B) :
    SubexpFlatAdd.encode (ofBits B bits) = bits := by
  rw [ofBits, dite_eq_left hbits, encode_split]

theorem exists_encoded (B : ℕ) (bits : List Bool) (hbits : bits.length = 4 * B) :
    ∃ a : Quad (Word B), SubexpFlatAdd.encode a = bits :=
  ⟨ofBits B bits, encode_ofBits B bits hbits⟩

end SubexponentialSAT.SubexpRawQuartic

end OAI.Algorithms
