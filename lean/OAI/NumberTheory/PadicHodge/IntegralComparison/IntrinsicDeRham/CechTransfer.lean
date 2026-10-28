import OAI.NumberTheory.PadicHodge.IntegralComparison.IntrinsicDeRham.CechComplex
import OAI.NumberTheory.PadicHodge.IntegralComparison.Cech.ComplexBaseChange
import OAI.NumberTheory.PadicHodge.IntegralComparison.FiniteEtale.TraceRank
import Mathlib.Algebra.Homology.Additive

/-! # Cech Transfer -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.IntrinsicDeRham.CechTransfer.Intrinsic

noncomputable section

/-! Pullback and finite étale trace on the actual de Rham Čech
bicomplexes. Their composite is the geometric finite-flat rank. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.TopologicalSpace

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open OAI.NumberTheory.PadicHodge.IntegralComparison.IntrinsicDeRham.CechComplex.Intrinsic

universe u

variable (R : Type u) [CommRing R]
  (X Y : Over (Spec (CommRingCat.of R))) (f : X ⟶ Y)
  {ι : Type u} (U : ι → Y.left.Opens)

local instance opens_finiteLimits : PreservesFiniteLimits (Opens.map f.left.base) := by
  change PreservesFiniteLimits (OrderHom.ofClass f.left.base.frameHom).toFunctor
  infer_instance

abbrev inverseCover : ι → X.left.Opens := fun i => f.left ⁻¹ᵁ U i

def imageBicomplex : HomologicalComplex₂ (ModuleCat.{u} R) (.up ℕ) (.up ℕ) :=
  (Cech.ComplexBaseChange.bicomplexFunctor U).obj
    (((CechComplex.Intrinsic.presheaves R Y).mapHomologicalComplex (.up ℕ)).obj
      (((AlgebraicGeometry.Crystalline.Cohomology.DeRhamPullbackTo.DeRhamPullback.directImage f).mapHomologicalComplex (.up ℕ)).obj
        (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.sheafComplex R X)))

def imageIso : imageBicomplex R X Y f U ≅ CechComplex.Intrinsic.bicomplex R X (inverseCover R X Y f U) :=
  Cech.ComplexBaseChange.bicomplexIso (Opens.map f.left.base) U (CechComplex.Intrinsic.presheafComplex R X)

def pullbackToImage : CechComplex.Intrinsic.bicomplex R Y U ⟶ imageBicomplex R X Y f U :=
  (Cech.ComplexBaseChange.bicomplexFunctor U).map
    (((CechComplex.Intrinsic.presheaves R Y).mapHomologicalComplex (.up ℕ)).map (AlgebraicGeometry.Crystalline.Cohomology.DeRhamPullbackTo.DeRhamPullback.sheafDirectImage f))

def pullback : CechComplex.Intrinsic.bicomplex R Y U ⟶ CechComplex.Intrinsic.bicomplex R X (inverseCover R X Y f U) :=
  pullbackToImage R X Y f U ≫ (imageIso R X Y f U).hom

variable [IsFinite f.left] [Etale f.left] [IsProper Y.hom] [Smooth Y.hom]

def traceFromImage : imageBicomplex R X Y f U ⟶ CechComplex.Intrinsic.bicomplex R Y U :=
  (Cech.ComplexBaseChange.bicomplexFunctor U).map
    (((CechComplex.Intrinsic.presheaves R Y).mapHomologicalComplex (.up ℕ)).map
      (FiniteEtale.DeRhamSheafTrace.trace R X Y f))

def trace : CechComplex.Intrinsic.bicomplex R X (inverseCover R X Y f U) ⟶ CechComplex.Intrinsic.bicomplex R Y U :=
  (imageIso R X Y f U).inv ≫ traceFromImage R X Y f U

local instance cech_additive :
    (Cech.ComplexBaseChange.bicomplexFunctor (A := ModuleCat.{u} R) U).Additive :=
  inferInstanceAs (((FormalCoproduct.cochainComplexFunctor
    (A := ModuleCat.{u} R) (FormalCoproduct.mk ι U).cech).mapHomologicalComplex (.up ℕ)).Additive)

theorem pullback_trace [PreconnectedSpace Y.left] (y : Y.left) :
    pullback R X Y f U ≫ trace R X Y f U =
      f.left.finrank y • 𝟙 (CechComplex.Intrinsic.bicomplex R Y U) := by
  unfold pullback trace
  rw [Category.assoc, ← Category.assoc (imageIso R X Y f U).hom,
    Iso.hom_inv_id, Category.id_comp]
  change (Cech.ComplexBaseChange.bicomplexFunctor U).map _ ≫
    (Cech.ComplexBaseChange.bicomplexFunctor U).map _ = _
  rw [← Functor.map_comp, ← Functor.map_comp, FiniteEtale.TraceRank.pullback_trace R X Y f y]
  simp only [Functor.map_nsmul]
  exact (congrArg (fun a => f.left.finrank y • (Cech.ComplexBaseChange.bicomplexFunctor U).map a)
    (((CechComplex.Intrinsic.presheaves R Y).mapHomologicalComplex (.up ℕ)).map_id (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.sheafComplex R Y))).trans
      (congrArg (fun a => f.left.finrank y • a)
        ((Cech.ComplexBaseChange.bicomplexFunctor U).map_id (CechComplex.Intrinsic.presheafComplex R Y)))

def totalPullback : CechComplex.Intrinsic.total R Y U ⟶ CechComplex.Intrinsic.total R X (inverseCover R X Y f U) :=
  HomologicalComplex₂.total.map (pullback R X Y f U) (.up ℕ)

def totalTrace : CechComplex.Intrinsic.total R X (inverseCover R X Y f U) ⟶ CechComplex.Intrinsic.total R Y U :=
  HomologicalComplex₂.total.map (trace R X Y f U) (.up ℕ)

private theorem total_nsmul_id
    (K : HomologicalComplex₂ (ModuleCat.{u} R) (.up ℕ) (.up ℕ)) (d : ℕ) :
    HomologicalComplex₂.total.map (d • 𝟙 K) (.up ℕ) = d • 𝟙 (K.total (.up ℕ)) := by
  ext n : 1
  apply HomologicalComplex₂.total.hom_ext
  intro i j hij
  simp only [HomologicalComplex₂.ιTotal_map, HomologicalComplex.nsmul_f_apply,
    HomologicalComplex.id_f, Preadditive.nsmul_comp, Preadditive.comp_nsmul,
    Category.id_comp, Category.comp_id]

theorem total_pullback_trace [PreconnectedSpace Y.left] (y : Y.left) :
    totalPullback R X Y f U ≫ totalTrace R X Y f U =
      f.left.finrank y • 𝟙 (CechComplex.Intrinsic.total R Y U) := by
  rw [totalPullback, totalTrace, ← HomologicalComplex₂.total.map_comp,
    pullback_trace R X Y f U y]
  exact total_nsmul_id R (CechComplex.Intrinsic.bicomplex R Y U) (f.left.finrank y)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.IntrinsicDeRham.CechTransfer.Intrinsic
