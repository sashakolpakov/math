import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.Correspondences
import Mathlib.AlgebraicGeometry.AlgClosed.Basic
import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
import Mathlib.Data.Fintype.EquivFin

/-! # Neighbors -/

namespace OAI.AlgebraicGeometry.AbelianScheme.TateComparison

noncomputable section

/-! Geometric neighbor multisets, with finiteness derived from the actual
finite cover. Different cover points retain repeated target points. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u

/-- A finite scheme over an algebraically closed field has finitely many
field-valued points. The proof uses its actual finite topological fiber. -/
theorem Neighbors.finite_field_sections {k : Type u} [Field k] [IsAlgClosed k]
    {Y : Scheme.{u}} (p : Y ⟶ Spec (.of k)) [IsFinite p] :
    Finite {a : Spec (.of k) ⟶ Y // a ≫ p = 𝟙 _} := by
  have hfin := p.finite_preimage_singleton (default : Spec (.of k))
  have hall : p ⁻¹' ({default} : Set (Spec (.of k))) = Set.univ := by
    ext y
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_univ, iff_true]
    exact Subsingleton.elim _ _
  rw [hall] at hfin
  let : Finite Y := Set.finite_univ_iff.mp hfin
  exact Finite.of_equiv (closedPoints Y) (pointEquivClosedPoint p).symm

variable {B : Scheme.{u}} {X : Over B} (C : Correspondences.EtaleCorrespondence X)
  {k : Type u} [Field k] [IsAlgClosed k]
  (s : Spec (.of k) ⟶ B) (x : Over.mk s ⟶ X)

/-- Branches are exactly sections of the scheme-theoretic geometric fiber. -/
def Correspondences.EtaleCorrespondence.fiberSectionEquiv : C.Fiber x ≃
    {a : Spec (.of k) ⟶ pullback C.source.left x.left //
      a ≫ pullback.snd C.source.left x.left = 𝟙 _} where
  toFun c := ⟨pullback.lift c.val.left (𝟙 _)
    (by simpa only [Category.id_comp, Over.comp_left] using
      congrArg (fun f => f.left) c.property),
    pullback.lift_snd _ _ _⟩
  invFun a := ⟨Over.homMk (a.val ≫ pullback.fst C.source.left x.left) (by
    calc
      _ = a.val ≫ pullback.fst C.source.left x.left ≫ C.source.left ≫ X.hom := by
        rw [C.source.w]
        simp only [Category.assoc]
      _ = a.val ≫ pullback.snd C.source.left x.left ≫ x.left ≫ X.hom := by
        rw [← Category.assoc (pullback.fst C.source.left x.left), pullback.condition]
        simp only [Category.assoc]
      _ = s := by
        rw [← Category.assoc a.val, a.property, Category.id_comp, x.w]
        rfl), by
    apply Over.OverMorphism.ext
    change (a.val ≫ pullback.fst C.source.left x.left) ≫ C.source.left = x.left
    rw [Category.assoc, pullback.condition, ← Category.assoc, a.property,
      Category.id_comp]⟩
  left_inv c := by
    apply Subtype.ext
    apply Over.OverMorphism.ext
    exact pullback.lift_fst _ _ _
  right_inv a := by
    apply Subtype.ext
    apply pullback.hom_ext
    · exact pullback.lift_fst _ _ _
    · exact (pullback.lift_snd _ _ _).trans a.property.symm

instance Correspondences.EtaleCorrespondence.finiteFiber : Finite (C.Fiber x) := by
  have : IsFinite (pullback.snd C.source.left x.left) := inferInstance
  have := Neighbors.finite_field_sections (pullback.snd C.source.left x.left)
  exact Finite.of_equiv _ (C.fiberSectionEquiv s x).symm

/-- The geometric multiset is obtained by enumerating source-fiber points
once each and mapping them by the target morphism. -/
def Correspondences.EtaleCorrespondence.neighbors : Multiset (Over.mk s ⟶ X) :=
  let : Fintype (C.Fiber x) := Fintype.ofFinite _
  (Finset.univ : Finset (C.Fiber x)).val.map (fun c => C.endpoint c)

theorem Correspondences.EtaleCorrespondence.mem_neighbors (y : Over.mk s ⟶ X) :
    y ∈ C.neighbors s x ↔ ∃ c : C.Fiber x, C.endpoint c = y := by
  classical
  let : Fintype (C.Fiber x) := Fintype.ofFinite _
  simp only [Correspondences.EtaleCorrespondence.neighbors, Multiset.mem_map, Finset.mem_val, Finset.mem_univ, true_and]

/-- Composition counts actual chains of source-fiber points, retaining
their repeated final targets. This is proved before any Hecke classification. -/
theorem Correspondences.EtaleCorrespondence.neighbors_comp (D : Correspondences.EtaleCorrespondence X) :
    (C.comp D).neighbors s x = (C.neighbors s x).bind (D.neighbors s) := by
  classical
  let : Fintype (C.Fiber x) := Fintype.ofFinite _
  let : ∀ y : Over.mk s ⟶ X, Fintype (D.Fiber y) := fun y => Fintype.ofFinite _
  let : Finite ((C.comp D).Fiber x) := Correspondences.EtaleCorrespondence.finiteFiber (C.comp D) s x
  let : Fintype ((C.comp D).Fiber x) := Fintype.ofFinite _
  let e := C.compFiberEquiv D x
  have he := Multiset.map_univ_val_equiv e
  calc
    (C.comp D).neighbors s x =
        (Finset.univ : Finset (C.Chain D x)).val.map (fun z => D.endpoint z.2) := by
      change (Finset.univ : Finset ((C.comp D).Fiber x)).val.map
        (fun z => (C.comp D).endpoint z) = _
      rw [← he, Multiset.map_map]
      apply Multiset.map_congr rfl
      intro z _
      exact (C.compFiberEquiv_endpoint D x z).symm
    _ = (C.neighbors s x).bind (D.neighbors s) := by
      change ((Finset.univ : Finset (C.Fiber x)).val.sigma
        (fun c => (Finset.univ : Finset (D.Fiber (C.endpoint c))).val)).map
          (fun z => D.endpoint z.2) = _
      simp only [Correspondences.EtaleCorrespondence.neighbors, Multiset.sigma, Multiset.map_bind,
        Multiset.map_map, Multiset.bind_map, Function.comp_def]

/-- A correspondence whose source is an isomorphism has its single graph neighbor. -/
theorem Correspondences.EtaleCorrespondence.neighbors_of_source_iso [IsIso C.source] :
    C.neighbors s x = {x ≫ inv C.source ≫ C.target} := by
  classical
  let : Fintype (C.Fiber x) := Fintype.ofFinite _
  let c : C.Fiber x := ⟨x ≫ inv C.source, by simp⟩
  have hc : ∀ z : C.Fiber x, z = c := by
    intro z
    apply Subtype.ext
    apply (cancel_mono C.source).mp
    exact z.property.trans c.property.symm
  have hu : (Finset.univ : Finset (C.Fiber x)) = {c} := by
    ext z
    simp only [Finset.mem_univ, Finset.mem_singleton, true_iff]
    exact hc z
  change (Finset.univ : Finset (C.Fiber x)).val.map C.endpoint = _
  rw [hu]
  simp only [Finset.singleton_val, Multiset.map_singleton]
  rfl

end

end OAI.AlgebraicGeometry.AbelianScheme.TateComparison
