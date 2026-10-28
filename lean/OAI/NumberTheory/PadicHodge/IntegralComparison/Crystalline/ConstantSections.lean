import OAI.NumberTheory.PadicHodge.IntegralComparison.Sheafified.PresheafSections
import OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.StructureDescent

/-! # Constant Sections -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ConstantSections

noncomputable section

/-! Constants and their values in the original crystalline degree-zero cohomology. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

universe u

open OAI.NumberTheory.PadicHodge.IntegralComparison.BigCrystallineSite

variable {p : ℕ} {B : Type u} [CommRing B] {J : Ideal B} {δ : DividedPowers J}
  {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of B))

local notation "R" => OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction.Coeff (B := B)
local notation "P" => OAI.NumberTheory.PadicHodge.IntegralComparison.BigCrystallineCohomology.largePresheaf (p := p) (J := J) (δ := δ) f

abbrev Sections := ((Functor.const (BigCrystallineSite.Object p B J δ f)ᵒᵖ).obj (ModuleCat.of R R) ⟶ P)

def value (s : Sections (p := p) (J := J) (δ := δ) f) (U : BigCrystallineSite.Object p B J δ f) : U.ring :=
  (s.app (op U) (1 : R)).down

theorem value_natural (s : Sections (p := p) (J := J) (δ := δ) f)
    {U V : BigCrystallineSite.Object p B J δ f} (g : U ⟶ V) : g.ringMap (value f s V) = value f s U := by
  have h := congrArg (fun a => (a (1 : R)).down) (s.naturality g.op)
  exact h.symm

def unit : Sections (p := p) (J := J) (δ := δ) f where
  app U := ModuleCat.ofHom (LinearMap.toSpanSingleton R ((P).obj U)
    (ULift.up (1 : U.unop.ring)))
  naturality {U V} g := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext_ring
    change ULift.up (V.unop.base (1 : B) * 1) =
      ULift.up (g.unop.ringMap (U.unop.base (1 : B) * 1))
    rw [map_one, map_one, one_mul, one_mul]
    exact congrArg ULift.up g.unop.ringMap.toRingHom.map_one.symm

def constants : R →ₗ[R] Sections (p := p) (J := J) (δ := δ) f :=
  LinearMap.toSpanSingleton R _ (unit f)

theorem value_constants (w : R) (U : BigCrystallineSite.Object p B J δ f) :
    value f (constants f w) U = U.base w.down := by
  change U.base w.down * (U.base (1 : B) * 1) = U.base w.down
  rw [map_one, one_mul, mul_one]

theorem ext (s t : Sections (p := p) (J := J) (δ := δ) f)
    (h : ∀ U, value f s U = value f t U) : s = t := by
  apply NatTrans.ext
  funext U
  apply ModuleCat.hom_ext
  apply LinearMap.ext_ring
  apply ULift.ext
  exact h U.unop

def cohomologyEquiv :
    BigCrystallineCohomology.Cohomology (p := p) (J := J) (δ := δ) f 0 ≃ₗ[R]
      Sections (p := p) (J := J) (δ := δ) f :=
  Sheafified.PresheafSections.degreeZeroLinearEquiv R BigCrystallineSite.Object.topology P
    (StructureDescent.largePresheaf_isSheaf f)

def cohomologyConstants : R →ₗ[R]
    BigCrystallineCohomology.Cohomology (p := p) (J := J) (δ := δ) f 0 :=
  (cohomologyEquiv f).symm.toLinearMap.comp (constants f)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ConstantSections
