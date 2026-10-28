import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Finite.NeutralGroup
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Kernel.Splitting

/-! # Neutral Functor -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.NeutralFunctor.CM

noncomputable section

/-! The constructed neutral factor is functorial for actual morphisms of
finite commutative group schemes. Thus original block retractions restrict
to retractions of their connected factors. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj
open OAI.AlgebraicGeometry.Picard.PoincareBundle.Kernel.Scheme

open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Finite.GroupRetraction.CM OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Finite.GroupDecomposition.CM OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Finite.NeutralGroup.CM

universe u
variable {k : Type u} [Field k] [IsAlgClosed k]
  (A B : Grp (Over (Spec (.of k)))) [IsFinite A.X.hom] [IsFinite B.X.hom]
  [IsCommMonObj A.X] [IsCommMonObj B.X]

attribute [local instance] Picard.PoincareBundle.Kernel.Scheme.kernelGroup

theorem preserves_neutral (f : A ⟶ B) :
    (Picard.PoincareBundle.Kernel.Scheme.kernelInclusion (Finite.GroupRetraction.CM.componentMap A) ≫ f.hom.hom) ≫ Finite.GroupRetraction.CM.componentMap B = 1 := by
  let : IsFinite (Finite.GroupDecomposition.CM.neutralPart A).X.hom := Finite.NeutralGroup.CM.neutral_finite A
  apply Finite.PointRetraction.CM.hom_ext_to_constant (Finite.GroupDecomposition.CM.neutralPart A).X
    (Over.mk (𝟙 (Spec (.of k))) ⟶ B.X)
  intro p
  exact (congrArg (fun w : Over.mk (𝟙 (Spec (.of k))) ⟶ Picard.PoincareBundle.Kernel.Scheme.kernelObject (Finite.GroupRetraction.CM.componentMap A) =>
    w ≫ ((Picard.PoincareBundle.Kernel.Scheme.kernelInclusion (Finite.GroupRetraction.CM.componentMap A) ≫ f.hom.hom) ≫ Finite.GroupRetraction.CM.componentMap B))
      (Finite.GroupDecomposition.CM.neutral_points_trivial A p)).trans
    ((MonObj.one_comp ((Picard.PoincareBundle.Kernel.Scheme.kernelInclusion (Finite.GroupRetraction.CM.componentMap A) ≫ f.hom.hom) ≫ Finite.GroupRetraction.CM.componentMap B)).trans
      (MonObj.comp_one p).symm)

def schemeMap (f : A ⟶ B) : Picard.PoincareBundle.Kernel.Scheme.kernelObject (Finite.GroupRetraction.CM.componentMap A) ⟶ Picard.PoincareBundle.Kernel.Scheme.kernelObject (Finite.GroupRetraction.CM.componentMap B) :=
  (Picard.PoincareBundle.Kernel.Scheme.kernelPointsEquiv (Finite.GroupRetraction.CM.componentMap B) (Picard.PoincareBundle.Kernel.Scheme.kernelObject (Finite.GroupRetraction.CM.componentMap A))).symm
    ⟨Picard.PoincareBundle.Kernel.Scheme.kernelInclusion (Finite.GroupRetraction.CM.componentMap A) ≫ f.hom.hom, preserves_neutral A B f⟩

theorem schemeMap_inclusion (f : A ⟶ B) :
    schemeMap A B f ≫ Picard.PoincareBundle.Kernel.Scheme.kernelInclusion (Finite.GroupRetraction.CM.componentMap B) =
      Picard.PoincareBundle.Kernel.Scheme.kernelInclusion (Finite.GroupRetraction.CM.componentMap A) ≫ f.hom.hom :=
  CategoryTheory.Limits.pullback.lift_fst _ _ _

instance schemeMap_isMonHom (f : A ⟶ B) : IsMonHom (schemeMap A B f) := by
  have : IsMonHom (schemeMap A B f ≫ Picard.PoincareBundle.Kernel.Scheme.kernelInclusion (Finite.GroupRetraction.CM.componentMap B)) := by
    rw [schemeMap_inclusion]
    infer_instance
  exact Picard.PoincareBundle.Kernel.Splitting.isMonHom_of_mono_postcomp _
    (Picard.PoincareBundle.Kernel.Scheme.kernelInclusion (Finite.GroupRetraction.CM.componentMap B))

def map (f : A ⟶ B) : Finite.GroupDecomposition.CM.neutralPart A ⟶ Finite.GroupDecomposition.CM.neutralPart B :=
  Grp.ofHom (A := Picard.PoincareBundle.Kernel.Scheme.kernelObject (Finite.GroupRetraction.CM.componentMap A)) (B := Picard.PoincareBundle.Kernel.Scheme.kernelObject (Finite.GroupRetraction.CM.componentMap B))
    (schemeMap A B f)

theorem map_mono (f : A ⟶ B) [Mono f.hom.hom] : Mono (map A B f).hom.hom := by
  change Mono (schemeMap A B f)
  exact mono_of_mono_fac (schemeMap_inclusion A B f)

theorem map_id : map A A (𝟙 A) = 𝟙 (Finite.GroupDecomposition.CM.neutralPart A) := by
  apply Grp.hom_ext
  change schemeMap A A (𝟙 A) = 𝟙 (Picard.PoincareBundle.Kernel.Scheme.kernelObject (Finite.GroupRetraction.CM.componentMap A))
  apply (cancel_mono (Picard.PoincareBundle.Kernel.Scheme.kernelInclusion (Finite.GroupRetraction.CM.componentMap A))).mp
  rw [schemeMap_inclusion]
  exact (Category.comp_id _).trans (Category.id_comp _).symm

theorem map_comp (C : Grp (Over (Spec (.of k)))) [IsFinite C.X.hom] [IsCommMonObj C.X]
    (f : A ⟶ B) (g : B ⟶ C) : map A C (f ≫ g) = map A B f ≫ map B C g := by
  apply Grp.hom_ext
  change schemeMap A C (f ≫ g) = schemeMap A B f ≫ schemeMap B C g
  apply (cancel_mono (Picard.PoincareBundle.Kernel.Scheme.kernelInclusion (Finite.GroupRetraction.CM.componentMap C))).mp
  rw [schemeMap_inclusion, Category.assoc, schemeMap_inclusion, ← Category.assoc, schemeMap_inclusion]
  exact (Category.assoc _ _ _).symm

theorem preserves_retraction (s : B ⟶ A) (r : A ⟶ B) (h : s ≫ r = 𝟙 B) :
    map B A s ≫ map A B r = 𝟙 (Finite.GroupDecomposition.CM.neutralPart B) := by
  rw [← map_comp, h, map_id]

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.NeutralFunctor.CM
