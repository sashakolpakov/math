import OAI.NumberTheory.PadicHodge.GeometricComparison.OrdinaryDeRhamIs
import OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothWitt.ReductionComplex

/-! # Witt Coefficient Reduction Iso -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.Smooth.WittCoefficientReductionIso.SmoothWittCoefficientReductionIso

noncomputable section

/-! The canonical coefficient reduction map is an isomorphism on an
actual etale-coordinate smooth Witt algebra, by the original quotient comparison. -/

open _root_.CategoryTheory

universe u
variable (p : ℕ) [Fact p.Prime] (k A σ : Type u) [Field k] [CharP k p]
  [CommRing A] [Algebra (WittVector p k) A] [Module.Flat (WittVector p k) A]
  [LinearOrder σ] [Fintype σ] [Algebra (MvPolynomial σ (WittVector p k)) A]
  [IsScalarTower (WittVector p k) (MvPolynomial σ (WittVector p k)) A]
  [Algebra.Etale (MvPolynomial σ (WittVector p k)) A] (n : ℕ)

local notation "W" => WittVector p k
local notation "Ip" => (Ideal.span {(p : WittVector p k)}) ^ (n + 1)
local notation "JA" => (Ideal.span {(p : A)}) ^ (n + 1)
local notation "An" => OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothWitt.FrameRing.Ring p A n
local instance frameAlgebra : Algebra W An := (IntegralComparison.SmoothWitt.FrameRing.base p k A n).toAlgebra

def quotientMap : A →ₐ[W] An :=
  { toRingHom := Ideal.Quotient.mk JA, commutes' := fun _ => rfl }

variable (hAn : ∀ r, r ∈ (Ideal.span {(p : WittVector p k)}) ^ (n + 1) →
  algebraMap (WittVector p k) (IntegralComparison.SmoothWitt.FrameRing.Ring p A n) r = 0)

include σ in
omit [CharP k p] [Module.Flat (WittVector p k) A] [Fintype σ] in
theorem isIso : IsIso (OrdinaryDeRhamIs.OrdinaryDeRhamCoefficientReduction.map W Ip
    (CommAlgCat.ofHom (quotientMap p k A n)) hAn) := by
  apply OrdinaryDeRhamIs.OrdinaryDeRhamCoefficientReduction.isIso_of_comparison W Ip
    (CommAlgCat.ofHom (quotientMap p k A n)) hAn (IntegralComparison.SmoothWitt.ReductionComplex.quotientIso p k A σ n)
  apply HomologicalComplex.Hom.ext
  funext m
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro ω
  exact IntegralComparison.SmoothWitt.ReductionComplex.reductionMap_apply p k A σ n m ω

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.Smooth.WittCoefficientReductionIso.SmoothWittCoefficientReductionIso
