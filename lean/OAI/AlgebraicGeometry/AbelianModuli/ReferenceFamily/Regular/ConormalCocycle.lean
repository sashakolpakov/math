import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Complex.ConormalCocycle
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Constructed.IdentityConormalNaturality
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Complex.CoefficientDetection

/-! # Conormal Cocycle -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Regular.ConormalCocycle

noncomputable section

/-! The actual conormal reference-change cocycle law holds over every
reduced finite-type complex coefficient algebra, detected by its original
complex characters. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

attribute [local implicit_reducible] EtaleSplittingAt.EtaleSplitting.affineOver

variable (A : Over Foundations.Scheme.ProjectiveSpace.complexBase) [IsIntegral A.left] [Smooth A.hom] [GrpObj A]
    (C : Type) [CommRing C] [Algebra ℂ C] [Algebra.FiniteType ℂ C] [IsReduced C]

theorem regularConormalReference_cocycle (a b c : EtaleSplittingAt.EtaleSplitting.affineOver ℂ (DualNumber C) ⟶ A)
    (hab : Dual.CoefficientSchemeTests.dualCoefficientOrigin ℂ C ≫ b = Dual.CoefficientSchemeTests.dualCoefficientOrigin ℂ C ≫ a)
    (hbc : Dual.CoefficientSchemeTests.dualCoefficientOrigin ℂ C ≫ c = Dual.CoefficientSchemeTests.dualCoefficientOrigin ℂ C ≫ b) :
    Constructed.IdentityConormal.constructedIdentityLiftConormalEquiv ℂ A C a ⟨b, hab⟩ +
        Constructed.IdentityConormal.constructedIdentityLiftConormalEquiv ℂ A C b ⟨c, hbc⟩ =
      Constructed.IdentityConormal.constructedIdentityLiftConormalEquiv ℂ A C a ⟨c, hbc.trans hab⟩ := by
  apply LinearMap.ext
  intro z
  apply Complex.CoefficientDetection.complexCoefficientCharacters_ext C
  intro q
  let t := Affine.AlgebraAutomorphismNaturality.affineOverAlgHom ℂ (DualNumber C) (DualNumber ℂ) (Dual.NumberCoefficients.dualNumberAlgMap q)
  let u := Constructed.IdentityConormalNaturality.constructedIdentityRestrictedLift ℂ A C ℂ q a ⟨b, hab⟩
  let v := Constructed.IdentityConormalNaturality.constructedIdentityRestrictedLift ℂ A C ℂ q b ⟨c, hbc⟩
  have habq : Dual.CoefficientSchemeTests.dualCoefficientOrigin ℂ ℂ ≫ (t ≫ b) = Dual.CoefficientSchemeTests.dualCoefficientOrigin ℂ ℂ ≫ (t ≫ a) := u.property
  have hbcq : Dual.CoefficientSchemeTests.dualCoefficientOrigin ℂ ℂ ≫ (t ≫ c) = Dual.CoefficientSchemeTests.dualCoefficientOrigin ℂ ℂ ≫ (t ≫ b) := v.property
  have h₁ := Constructed.IdentityConormalNaturality.constructedIdentityLiftConormalEquiv_natural ℂ A C ℂ q a ⟨b, hab⟩ z
  have h₂ := Constructed.IdentityConormalNaturality.constructedIdentityLiftConormalEquiv_natural ℂ A C ℂ q b ⟨c, hbc⟩ z
  have h₃ := Constructed.IdentityConormalNaturality.constructedIdentityLiftConormalEquiv_natural ℂ A C ℂ q a ⟨c, hbc.trans hab⟩ z
  have h := LinearMap.congr_fun (Complex.ConormalCocycle.complexConormalReference_cocycle A (t ≫ a) (t ≫ b) (t ≫ c) habq hbcq) z
  change q (_ + _) = _
  rw [map_add]
  exact (congrArg₂ (· + ·) h₁.symm h₂.symm).trans (h.trans h₃)

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Regular.ConormalCocycle
