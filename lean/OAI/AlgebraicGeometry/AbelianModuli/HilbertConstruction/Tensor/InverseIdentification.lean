import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.LineBundle.ClassMonoid

/-! # Inverse Identification -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! Two line bundles that are complementary tensor inverses of the same bundle are isomorphic. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

theorem Line.Bundles.LineBundle.iso_of_common_tensor_inverse {X : Scheme.{u}} (L M N : Line.Bundles.LineBundle X)
    (hLN : Nonempty ((L.tensor N).sheaf ≅ Line.Bundles.structureModule X))
    (hNM : Nonempty ((N.tensor M).sheaf ≅ Line.Bundles.structureModule X)) : Nonempty (L.sheaf ≅ M.sheaf) := by
  have h₁ : Line.Bundles.LineBundle.classOf L * Line.Bundles.LineBundle.classOf N = 1 := Quotient.sound hLN
  have h₂ : Line.Bundles.LineBundle.classOf N * Line.Bundles.LineBundle.classOf M = 1 := Quotient.sound hNM
  have he : Line.Bundles.LineBundle.classOf L = Line.Bundles.LineBundle.classOf M := by
    calc
      Line.Bundles.LineBundle.classOf L = Line.Bundles.LineBundle.classOf L * 1 := (mul_one _).symm
      _ = Line.Bundles.LineBundle.classOf L * (Line.Bundles.LineBundle.classOf N * Line.Bundles.LineBundle.classOf M) :=
        congrArg (fun q => Line.Bundles.LineBundle.classOf L * q) h₂.symm
      _ = (Line.Bundles.LineBundle.classOf L * Line.Bundles.LineBundle.classOf N) * Line.Bundles.LineBundle.classOf M := (mul_assoc _ _ _).symm
      _ = Line.Bundles.LineBundle.classOf M := by rw [h₁, one_mul]
  exact Quotient.exact he

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
