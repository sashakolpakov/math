import Mathlib.Algebra.Homology.Functor

/-! # Complex Assembly Quasi -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.ComplexAssemblyQuasi.ComplexAssembly

noncomputable section

/-!
# Assembling a functor of complexes

Objectwise complexes and natural chain maps assemble into a complex in
the functor category. A natural transformation that is a quasi-isomorphism
at every object remains a quasi-isomorphism after assembly.
-/

open _root_.CategoryTheory Limits

universe u v w z

variable {T : Type u} [Category.{v} T] {V : Type w} [Category.{z} V]

section Construction

variable [HasZeroMorphisms V] {ι : Type*} (c : ComplexShape ι)

def complex (F : T ⥤ HomologicalComplex V c) : HomologicalComplex (T ⥤ V) c where
  X i := F ⋙ HomologicalComplex.eval V c i
  d i j :=
    { app t := (F.obj t).d i j
      naturality _ _ f := (F.map f).comm i j }
  shape i j hij := by
    apply NatTrans.ext
    funext t
    exact (F.obj t).shape i j hij
  d_comp_d' i j k _ _ := by
    apply NatTrans.ext
    funext t
    exact (F.obj t).d_comp_d i j k

def map {F G : T ⥤ HomologicalComplex V c} (a : F ⟶ G) : complex c F ⟶ complex c G where
  f i :=
    { app t := (a.app t).f i
      naturality t s f := congrArg (fun h => h.f i) (a.naturality f) }
  comm' i j _ := by
    apply NatTrans.ext
    funext t
    exact (a.app t).comm i j

def functor : (T ⥤ HomologicalComplex V c) ⥤ HomologicalComplex (T ⥤ V) c where
  obj := complex c
  map := ComplexAssembly.map c
  map_id _ := by
    ext i t
    rfl
  map_comp _ _ := by
    ext i t
    rfl

local instance constPreservesZero : (Functor.const T : V ⥤ T ⥤ V).PreservesZeroMorphisms where
  map_zero _ _ := rfl

def constantIso (K : HomologicalComplex V c) :
    complex c ((Functor.const T).obj K) ≅
      ((Functor.const T).mapHomologicalComplex c).obj K :=
  Iso.refl _

def evaluationIso (F : T ⥤ HomologicalComplex V c) (t : T) :
    (((evaluation T V).obj t).mapHomologicalComplex c).obj (complex c F) ≅ F.obj t :=
  HomologicalComplex.Hom.isoOfComponents (fun _ => Iso.refl _) (by
    intro i j _
    change 𝟙 _ ≫ (F.obj t).d i j = (F.obj t).d i j ≫ 𝟙 _
    simp)

theorem evaluation_map {F G : T ⥤ HomologicalComplex V c} (a : F ⟶ G) (t : T) :
    (((evaluation T V).obj t).mapHomologicalComplex c).map (ComplexAssembly.map c a) ≫
      (evaluationIso c G t).hom = (evaluationIso c F t).hom ≫ a.app t := by
  ext i
  change (a.app t).f i ≫ 𝟙 _ = 𝟙 _ ≫ (a.app t).f i
  simp

end Construction

variable [Abelian V] {ι : Type*} (c : ComplexShape ι)

theorem map_quasiIso {F G : T ⥤ HomologicalComplex V c} (a : F ⟶ G)
    (ha : ∀ t, QuasiIso (a.app t)) : QuasiIso (ComplexAssembly.map c a) := by
  rw [HomologicalComplex.quasiIso_iff_evaluation]
  intro t
  let : QuasiIso (a.app t) := ha t
  exact quasiIso_of_arrow_mk_iso (a.app t)
    ((((evaluation T V).obj t).mapHomologicalComplex c).map (ComplexAssembly.map c a))
    (Arrow.isoMk (evaluationIso c F t) (evaluationIso c G t)
      (evaluation_map c a t).symm).symm

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.ComplexAssemblyQuasi.ComplexAssembly
