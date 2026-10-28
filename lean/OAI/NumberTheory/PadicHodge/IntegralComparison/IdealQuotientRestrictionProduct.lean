import OAI.NumberTheory.PadicHodge.GeometricComparison.IdealQuotientEq
import OAI.NumberTheory.PadicHodge.IntegralComparison.Module.IdealQuotientProduct

/-! # Ideal Quotient Restriction Product -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.IdealQuotientRestrictionProduct

noncomputable section

/-! The literal coefficient-quotient restriction isomorphism preserves
every bilinear product, with the extended coefficient ideal. -/

open _root_.CategoryTheory

universe u v w
variable (R : Type u) (S : Type v) [CommRing R] [CommRing S] [Algebra R S] (I : Ideal R)
  (M N P : ModuleCat.{w} S) (μ : M →ₗ[S] N →ₗ[S] P)

local notation "G" => ModuleCat.restrictScalars (algebraMap R S)
local notation "J" => I.map (algebraMap R S)
local instance restrictedModule (V : ModuleCat.{w} S) : Module R V := Module.compHom V (algebraMap R S)
local instance tower (V : ModuleCat.{w} S) : IsScalarTower R S V where
  smul_assoc r s x := by
    rw [Algebra.smul_def]
    exact mul_smul _ _ _

def restrictedPairing : (G).obj M →ₗ[R] (G).obj N →ₗ[R] (G).obj P := μ.restrictScalars₁₂ R R

theorem component_pairing
    (x : (IntegralComparison.Module.IdealQuotient.functor R I).obj ((G).obj M))
    (y : (IntegralComparison.Module.IdealQuotient.functor R I).obj ((G).obj N)) :
    (GeometricComparison.IdealQuotientEq.IdealQuotientRestriction.component R S I P).hom
        (IntegralComparison.Module.IdealQuotientProduct.pairing I (restrictedPairing R S M N P μ) x y) =
      IntegralComparison.Module.IdealQuotientProduct.pairing J μ
        ((GeometricComparison.IdealQuotientEq.IdealQuotientRestriction.component R S I M).hom x)
        ((GeometricComparison.IdealQuotientEq.IdealQuotientRestriction.component R S I N).hom y) := by
  obtain ⟨x, rfl⟩ := (I • ⊤ : Submodule R ((G).obj M)).mkQ_surjective x
  obtain ⟨y, rfl⟩ := (I • ⊤ : Submodule R ((G).obj N)).mkQ_surjective y
  rfl

omit M N P μ in
def isoOfEq (J' : Ideal S) (h : I.map (algebraMap R S) = J') :
    ModuleCat.restrictScalars (algebraMap R S) ⋙ IntegralComparison.Module.IdealQuotient.functor R I ≅
      IntegralComparison.Module.IdealQuotient.functor S J' ⋙ ModuleCat.restrictScalars (algebraMap R S) :=
  h ▸ GeometricComparison.IdealQuotientEq.IdealQuotientRestriction.iso R S I

omit N P μ in
theorem isoOfEq_mk (J' : Ideal S) (h : I.map (algebraMap R S) = J') (x : M) :
    ((isoOfEq R S I J' h).hom.app M) (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk x := by
  subst J'
  rfl

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.IdealQuotientRestrictionProduct
