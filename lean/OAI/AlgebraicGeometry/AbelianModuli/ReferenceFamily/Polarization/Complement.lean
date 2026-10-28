import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.ChernPairing
import OAI.AlgebraicGeometry.AbelianScheme.CentralAction.PolarizationEtale
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.IsogenyComplementGeometry

/-! # Complement -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Polarization.Complement

noncomputable section

/-! The original polarization type proves etaleness of its isogeny.
Finite-etale descent constructs its complementary isogeny directly on
the original dual scheme, without a projective embedding of that dual. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

variable {g N : ℕ} {δ : Fin g → ℕ}
    (A : HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N Foundations.Scheme.ProjectiveSpace.complexBase)

theorem polarization_isogeny_etale : Etale A.polarization.isogeny.hom.left :=
  AbelianScheme.CentralAction.PolarizationEtale.Construction.polarization_etale A.polarization.isogeny δ A.polarization.kernelType

theorem exists_polarization_complement :
    ∃ n : ℕ, 0 < n ∧ ∃ q : A.dual.abelian.scheme ⟶ A.abelian.scheme,
      IsMonHom q ∧ IsFinite q.left ∧ Etale q.left ∧ Surjective q.left ∧
      A.polarization.isogeny.hom ≫ q = (𝟙 A.abelian.scheme) ^ n ∧
      q ≫ A.polarization.isogeny.hom = (𝟙 A.dual.abelian.scheme) ^ n := by
  let : Etale A.polarization.isogeny.hom.left := polarization_isogeny_etale A
  obtain ⟨n, q, hn, hq, hfin, het, hsurj, hleft, hright, _⟩ :=
    PELModuli.IntegralModel.IsogenyComplementGeometry.exists_complementary_finite_etale_isogeny A.polarization.isogeny.hom
  exact ⟨n, hn, q, hq, hfin, het, hsurj, hleft, hright⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Polarization.Complement
