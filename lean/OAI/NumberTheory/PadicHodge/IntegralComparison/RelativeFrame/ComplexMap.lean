import OAI.NumberTheory.PadicHodge.IntegralComparison.RelativeFrame.FormNaturality

/-! # Complex Map -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.RelativeFrame.ComplexMap

noncomputable section

/-!
# IntegralComparison: the actual frame de Rham complex maps into the native relative resolution
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

open OAI.NumberTheory.PadicHodge.IntegralComparison.BigCrystallineSite OAI.NumberTheory.PadicHodge.IntegralComparison.RelativeFrame.FormMap OAI.NumberTheory.PadicHodge.IntegralComparison.RelativeFrame.FormNaturality

universe u v w

variable {C : Type v} [Category.{w} C] {p : ℕ} {B : Type u} [CommRing B]
  {J : Ideal B} {δ : DividedPowers J} {X : Scheme.{u}}
  {f : X ⟶ Spec (CommRingCat.of B)}
  (H Q : C ⥤ BigCrystallineSite.Object p B J δ f) (π : H ⟶ Q)
  (F : BigCrystallineSite.Object p B J δ f) (τ : H ⟶ (Functor.const C).obj F)

def frameComplex : CochainComplex (ModuleCat.{u} B) ℕ := by
  letI : Algebra B F.ring := F.base.toAlgebra
  exact AlgebraicGeometry.Crystalline.Cohomology.PD.DeRham.PDDeRham.complex B F.ring F.ideal F.dividedPowers

theorem frameComplex_d (n : ℕ) : (frameComplex F).d n (n + 1) =
    (Crystalline.DeRham.differential f n).app (op F) := by
  let : Algebra B F.ring := F.base.toAlgebra
  exact CochainComplex.of_d (fun n => ModuleCat.of B (AlgebraicGeometry.Crystalline.Cohomology.PD.DeRham.PDDeRham.Form B F.ring F.ideal F.dividedPowers n))
    (fun n => ModuleCat.ofHom (AlgebraicGeometry.Crystalline.Cohomology.PD.DeRham.PDDeRham.differential B F.ring F.ideal F.dividedPowers n)) n

def constantComplex : CochainComplex (Cᵒᵖ ⥤ ModuleCat.{u} B) ℕ :=
  ((Functor.const Cᵒᵖ).mapHomologicalComplex (ComplexShape.up ℕ)).obj (frameComplex F)

def map : constantComplex (C := C) F ⟶ RelativeCrystalline.ModuleComplex.complex H Q π where
  f n := FormNaturality.mapPresheaf H Q π F τ n
  comm' n m h := by
    change n + 1 = m at h
    subst m
    apply NatTrans.ext
    funext U
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro ω
    change ((RelativeCrystalline.ModuleComplex.complex H Q π).d n (n + 1)).app U
      (FormMap.map H Q π F τ U.unop n ω) =
        FormMap.map H Q π F τ U.unop (n + 1) ((frameComplex F).d n (n + 1) ω)
    rw [RelativeCrystalline.ModuleComplex.complex_d, frameComplex_d]
    exact (FormNaturality.map_differential H Q π F τ U.unop n ω).symm

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.RelativeFrame.ComplexMap
