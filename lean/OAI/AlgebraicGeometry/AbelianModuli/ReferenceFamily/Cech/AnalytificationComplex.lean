import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.CechDifferential
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Cech.GlobalModuleCoordinates

/-! # Analytification Complex -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Cech.AnalytificationComplex

noncomputable section

section

/-! Native holomorphic evaluation as an additive map from each degree
of the original algebraic Cech complex. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

variable (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) {I : Type} (U : I → V.carrier.Opens)

theorem nativeCechCochain_add (n : ℕ) (c d : Γ(TermModules.cechTermModule V.carrier U n, ⊤)) :
    Intrinsic.CechDifferential.nativeCechCochain V U n (c + d) = Intrinsic.CechDifferential.nativeCechCochain V U n c + Intrinsic.CechDifferential.nativeCechCochain V U n d := by
  funext i
  change Intrinsic.CechDifferential.nativeCechFunction V U n (c + d) i = Intrinsic.CechDifferential.nativeCechFunction V U n c i + Intrinsic.CechDifferential.nativeCechFunction V U n d i
  apply DFunLike.ext
  intro x
  change Intrinsic.CechDifferential.nativeCechFunction V U n (c + d) i x = Intrinsic.CechDifferential.nativeCechFunction V U n c i x + Intrinsic.CechDifferential.nativeCechFunction V U n d i x
  rw [Intrinsic.CechDifferential.nativeCechCochain_value, Intrinsic.CechDifferential.nativeCechCochain_value, Intrinsic.CechDifferential.nativeCechCochain_value]
  exact Intrinsic.CechDifferential.nativeCechValue_add V U n ⊤ c d i x.val _

def nativeCechCochainAddHom (n : ℕ) : Γ(TermModules.cechTermModule V.carrier U n, ⊤) →+
    DivisorClass.Chern.Abelian.CechCoordinates.AbelianCechCochain (DivisorClass.Chern.Holomorphic.Sheaves.holomorphicFunctionSheaf V.analyticModel V.analyticSpace).obj
      (Intrinsic.CechDifferential.nativeCechCover V U) n :=
  AddMonoidHom.mk' (Intrinsic.CechDifferential.nativeCechCochain V U n) (nativeCechCochain_add V U n)

def cechAnalytificationDegree (n : ℕ) :
    ((CategoryTheory.cechComplexFunctor U).obj (TermModules.structureAbelianSheaf V.carrier).obj).X n ⟶
      ((CategoryTheory.cechComplexFunctor (Intrinsic.CechDifferential.nativeCechCover V U)).obj
        (DivisorClass.Chern.Holomorphic.Sheaves.holomorphicFunctionSheaf V.analyticModel V.analyticSpace).obj).X n :=
  AddCommGrpCat.ofHom
    ((DivisorClass.Chern.Abelian.CechCoordinates.abelianCechCoordinates (DivisorClass.Chern.Holomorphic.Sheaves.holomorphicFunctionSheaf V.analyticModel V.analyticSpace).obj
      (Intrinsic.CechDifferential.nativeCechCover V U) n).symm.toAddMonoidHom.comp
        ((nativeCechCochainAddHom V U n).comp (GlobalModuleCoordinates.cechGlobalModuleCoordinates V.carrier U n).symm.toAddMonoidHom))

theorem cechAnalytificationDegree_coordinates (n : ℕ)
    (c : ((CategoryTheory.cechComplexFunctor U).obj (TermModules.structureAbelianSheaf V.carrier).obj).X n) :
    DivisorClass.Chern.Abelian.CechCoordinates.abelianCechCoordinates (DivisorClass.Chern.Holomorphic.Sheaves.holomorphicFunctionSheaf V.analyticModel V.analyticSpace).obj
      (Intrinsic.CechDifferential.nativeCechCover V U) n (cechAnalytificationDegree V U n c) =
        Intrinsic.CechDifferential.nativeCechCochain V U n ((GlobalModuleCoordinates.cechGlobalModuleCoordinates V.carrier U n).symm c) :=
  (DivisorClass.Chern.Abelian.CechCoordinates.abelianCechCoordinates (DivisorClass.Chern.Holomorphic.Sheaves.holomorphicFunctionSheaf V.analyticModel V.analyticSpace).obj
    (Intrinsic.CechDifferential.nativeCechCover V U) n).apply_symm_apply _

end

/-! The original algebraic and native holomorphic Cech complexes are
linked by an actual cochain map given by regular-function evaluation. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

variable (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) {I : Type} (U : I → V.carrier.Opens)

theorem cechGlobalModuleCoordinates_symm_differential (n : ℕ)
    (c : ((CategoryTheory.cechComplexFunctor U).obj (TermModules.structureAbelianSheaf V.carrier).obj).X n) :
    (GlobalModuleCoordinates.cechGlobalModuleCoordinates V.carrier U (n + 1)).symm
      (((CategoryTheory.cechComplexFunctor U).obj (TermModules.structureAbelianSheaf V.carrier).obj).d n (n + 1) c) =
        (ModuleDifferential.cechModuleDifferential V.carrier U n).app ⊤ ((GlobalModuleCoordinates.cechGlobalModuleCoordinates V.carrier U n).symm c) := by
  apply (GlobalModuleCoordinates.cechGlobalModuleCoordinates V.carrier U (n + 1)).injective
  rw [AddEquiv.apply_symm_apply, GlobalModuleCoordinates.cechGlobalModuleCoordinates_differential, AddEquiv.apply_symm_apply]

theorem cechAnalytificationDegree_differential (n : ℕ) :
    cechAnalytificationDegree V U n ≫
        ((CategoryTheory.cechComplexFunctor (Intrinsic.CechDifferential.nativeCechCover V U)).obj
          (DivisorClass.Chern.Holomorphic.Sheaves.holomorphicFunctionSheaf V.analyticModel V.analyticSpace).obj).d n (n + 1) =
      ((CategoryTheory.cechComplexFunctor U).obj (TermModules.structureAbelianSheaf V.carrier).obj).d n (n + 1) ≫
        cechAnalytificationDegree V U (n + 1) := by
  ext c
  apply (DivisorClass.Chern.Abelian.CechCoordinates.abelianCechCoordinates (DivisorClass.Chern.Holomorphic.Sheaves.holomorphicFunctionSheaf V.analyticModel V.analyticSpace).obj
    (Intrinsic.CechDifferential.nativeCechCover V U) (n + 1)).injective
  change DivisorClass.Chern.Abelian.CechCoordinates.abelianCechCoordinates _ _ (n + 1)
    (((CategoryTheory.cechComplexFunctor (Intrinsic.CechDifferential.nativeCechCover V U)).obj
      (DivisorClass.Chern.Holomorphic.Sheaves.holomorphicFunctionSheaf V.analyticModel V.analyticSpace).obj).d n (n + 1)
        (cechAnalytificationDegree V U n c)) =
    DivisorClass.Chern.Abelian.CechCoordinates.abelianCechCoordinates _ _ (n + 1) (cechAnalytificationDegree V U (n + 1)
      (((CategoryTheory.cechComplexFunctor U).obj (TermModules.structureAbelianSheaf V.carrier).obj).d n (n + 1) c))
  rw [DivisorClass.Chern.Abelian.CechCoordinates.abelianCechCoordinates_d, cechAnalytificationDegree_coordinates,
    cechAnalytificationDegree_coordinates, cechGlobalModuleCoordinates_symm_differential]
  exact (Intrinsic.CechDifferential.nativeCechCochain_differential V U n _).symm

def cechAnalytificationComplex :
    (CategoryTheory.cechComplexFunctor U).obj (TermModules.structureAbelianSheaf V.carrier).obj ⟶
      (CategoryTheory.cechComplexFunctor (Intrinsic.CechDifferential.nativeCechCover V U)).obj
        (DivisorClass.Chern.Holomorphic.Sheaves.holomorphicFunctionSheaf V.analyticModel V.analyticSpace).obj where
  f := cechAnalytificationDegree V U
  comm' i j h := by
    change i + 1 = j at h
    subst j
    exact cechAnalytificationDegree_differential V U i

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Cech.AnalytificationComplex
