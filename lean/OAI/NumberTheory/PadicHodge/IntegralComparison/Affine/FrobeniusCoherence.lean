import OAI.NumberTheory.PadicHodge.IntegralComparison.Affine.FrobeniusLocalization
import OAI.NumberTheory.PadicHodge.IntegralComparison.Affine.LocalizingModule
import OAI.NumberTheory.PadicHodge.IntegralComparison.Frobenius.DeRhamFiniteness

/-! # Frobenius Coherence -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Affine.FrobeniusCoherence

noncomputable section

/-!
# IntegralComparison: actual Frobenius de Rham sheaf terms are coherent on finite étale-coordinate charts
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

universe u

variable (k C : Type u) [Field k] [Fintype k] [CommRing C] [Algebra k C]

theorem finiteTop [Algebra.FiniteType k C] (n : ℕ) :
    Module.Finite C ((FrobeniusSections.presheaf k C n).obj (op ⊤)) := by
  let : Module.Finite C (Frobenius.DeRhamComplex.forms k C n) :=
    Frobenius.DeRhamFiniteness.forms_finite k C n
  exact Module.Finite.of_surjective (FrobeniusSections.map k C ⊤ n).hom
    (FrobeniusSections.top_bijective k C n).surjective

variable (σ : Type u) [LinearOrder σ] [Algebra (MvPolynomial σ k) C]
  [IsScalarTower k (MvPolynomial σ k) C] [Algebra.FormallyEtale (MvPolynomial σ k) C]

include σ in
theorem quasicoherent (n : ℕ) :
    ((Frobenius.DeRhamGlobal.complex k (Crystalline.Presentation.affineScheme k C)).X n).IsQuasicoherent :=
  LocalizingModule.quasicoherent C
    ((Frobenius.DeRhamGlobal.presheafComplex k (Crystalline.Presentation.affineScheme k C)).X n)
    (fun c => FrobeniusLocalization.restriction k C σ c n)

include σ in
theorem finiteType [Algebra.FiniteType k C] (n : ℕ) :
    ((Frobenius.DeRhamGlobal.complex k (Crystalline.Presentation.affineScheme k C)).X n).IsFiniteType :=
  @LocalizingModule.finiteType C inferInstance
    ((Frobenius.DeRhamGlobal.presheafComplex k (Crystalline.Presentation.affineScheme k C)).X n)
    (fun c => FrobeniusLocalization.restriction k C σ c n) (finiteTop k C n)

omit [Algebra.FormallyEtale (MvPolynomial σ k) C] in
include σ in
theorem finiteType_etale [Fintype σ] [Algebra.Etale (MvPolynomial σ k) C] (n : ℕ) :
    ((Frobenius.DeRhamGlobal.complex k (Crystalline.Presentation.affineScheme k C)).X n).IsFiniteType := by
  let : Algebra.FiniteType k C := Algebra.FiniteType.trans (S := MvPolynomial σ k) inferInstance inferInstance
  exact finiteType k C σ n

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Affine.FrobeniusCoherence
