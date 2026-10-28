import OAI.NumberTheory.PadicHodge.IntegralComparison.Contravariant.ExactFunctorPositive
import OAI.NumberTheory.PadicHodge.IntegralComparison.Contravariant.ExactFunctorZero
import OAI.NumberTheory.PadicHodge.IntegralComparison.Contravariant.ResolutionCohomology

/-! # Exact Functor Cohomology -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Contravariant.ExactFunctorCohomology

noncomputable section

/-! The all-degree source-resolution comparison computes the original exact-functor map on Ext. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

open Abelian

universe u v u' v' z t

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{z} C]
  {D : Type u'} [Category.{v'} D] [Abelian D] [HasExt.{z} D]
  (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  (R : Type t) [CommRing R] [Linear R C] [Linear R D] [F.Linear R] (Y : C)
  (K : CochainComplex Cᵒᵖ ℕ) {Z : Cᵒᵖ} (ι : (CochainComplex.single₀ Cᵒᵖ).obj Z ⟶ K)
  (κ : (CochainComplex.single₀ Dᵒᵖ).obj (F.op.obj Z) ⟶
    (F.op.mapHomologicalComplex (.up ℕ)).obj K) (hκ : κ.f 0 = F.op.map (ι.f 0))
  [QuasiIso ι] [QuasiIso κ]
  (hK : ∀ a q, Subsingleton (Ext.{z} (K.X a).unop Y (q + 1)))
  (hL : ∀ a q, Subsingleton (Ext.{z}
    (((F.op.mapHomologicalComplex (.up ℕ)).obj K).X a).unop (F.obj Y) (q + 1)))

include hκ in
theorem homology (i : ℕ) : HomologicalComplex.homologyMap (ExactFunctorComplex.map F R Y K) i ≫
    (ResolutionCohomology.homologyIso R (F.obj Y)
      ((F.op.mapHomologicalComplex (.up ℕ)).obj K) κ hL i).hom =
        (ResolutionCohomology.homologyIso R Y K ι hK i).hom ≫
          IntegralComparison.Ext.SourceExactFunctorModule.component F R Y i Z := by
  cases i with
  | zero => exact ExactFunctorZero.homology F R Y K ι κ hκ
  | succ i => exact ExactFunctorPositive.homology F R Y K ι κ hκ hK hL i

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Contravariant.ExactFunctorCohomology
