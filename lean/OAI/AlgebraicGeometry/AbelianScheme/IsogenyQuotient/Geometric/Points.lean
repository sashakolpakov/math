import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.EtaleDetection
import Mathlib.AlgebraicGeometry.Sites.Fpqc
import Mathlib.AlgebraicGeometry.AlgClosed.Basic
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-! # Points -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Geometric.Points.Construction

/-!
Geometric point lemmas for IsogenyQuotient. A surjective locally finite type morphism
is surjective on algebraically closed field points. Field extensions are
effective covers, so testing all algebraically closed fields also tests
arbitrary residue fields. No family-level polarization assertion is assumed.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

universe u

/-- Extension of fields is an fpqc cover of their spectra. -/
theorem field_spec_epi
    {K L : Type u} [Field K] [Field L] (i : K →+* L) :
    Epi (Spec.map (CommRingCat.ofHom i)) := by
  have : Flat (Spec.map (CommRingCat.ofHom i)) := by
    rw [Flat.SpecMap_iff]
    exact RingHom.Flat.of_isField (Field.toIsField K) i
  have : Surjective (Spec.map (CommRingCat.ofHom i)) :=
    ⟨Function.surjective_to_subsingleton _⟩
  infer_instance

/-- Surjective morphisms locally of finite type lift every geometric point. -/
theorem surjective_on_geometric_points
    {S : Scheme.{u}} {A B : Over S} (f : A ⟶ B)
    [Surjective f.left] [LocallyOfFiniteType f.left]
    (K : Type u) [Field K] [IsAlgClosed K]
    (s : Spec (CommRingCat.of K) ⟶ S) :
    Function.Surjective (fun a : Over.mk s ⟶ A => a ≫ f) := by
  intro b
  let Z := pullback f.left b.left
  let p : Z ⟶ Spec (CommRingCat.of K) := pullback.snd f.left b.left
  have hp : Surjective p := inferInstanceAs (Surjective (pullback.snd f.left b.left))
  have hpfin : LocallyOfFiniteType p :=
    inferInstanceAs (LocallyOfFiniteType (pullback.snd f.left b.left))
  have hnonempty : Nonempty Z := by
    obtain ⟨z, _⟩ := hp.1 (default : Spec (CommRingCat.of K))
    exact ⟨z⟩
  have : JacobsonSpace Z := LocallyOfFiniteType.jacobsonSpace p
  obtain ⟨z, _, hz⟩ := nonempty_inter_closedPoints
    (Set.univ_nonempty : (Set.univ : Set Z).Nonempty) isOpen_univ.isLocallyClosed
  change IsClosed ({z} : Set Z) at hz
  let a := pointOfClosedPoint p z hz ≫ pullback.fst f.left b.left
  have haf : a ≫ f.left = b.left := by
    dsimp [a]
    rw [Category.assoc, pullback.condition, ← Category.assoc]
    change (pointOfClosedPoint p z hz ≫ p) ≫ b.left = b.left
    rw [pointOfClosedPoint_comp, Category.id_comp]
  have has : a ≫ A.hom = s := by
    rw [← f.w, ← Category.assoc, haf, b.w]
    rfl
  exact ⟨Over.homMk a has, Over.OverMorphism.ext haf⟩

/-- Equality tested on algebraically closed field points also holds
on arbitrary field points, by descent along an algebraic closure. -/
theorem field_points_eq_of_geometric_points
    {S : Scheme.{u}} {X Y : Over S} (f g : X ⟶ Y)
    (h : ∀ (K : Type u) [Field K] [IsAlgClosed K]
      (s : Spec (CommRingCat.of K) ⟶ S) (x : Over.mk s ⟶ X),
        x ≫ f = x ≫ g)
    (K : Type u) [Field K]
    (s : Spec (CommRingCat.of K) ⟶ S) (x : Over.mk s ⟶ X) :
    x ≫ f = x ≫ g := by
  let i := Spec.map (CommRingCat.ofHom (algebraMap K (AlgebraicClosure K)))
  have : Epi i := field_spec_epi (algebraMap K (AlgebraicClosure K))
  let T : Over S := Over.mk (i ≫ s)
  let e : T ⟶ Over.mk s := Over.homMk i rfl
  have he := h (AlgebraicClosure K) (i ≫ s) (e ≫ x)
  apply Over.OverMorphism.ext
  apply (cancel_epi i).mp
  simpa [e, Over.comp_left, Category.assoc] using
    congrArg (fun a => a.left) he

theorem etale_ext_of_geometric_points
    {S : Scheme.{u}} {X Y : Over S} [Etale Y.hom] (f g : X ⟶ Y)
    (h : ∀ (K : Type u) [Field K] [IsAlgClosed K]
      (s : Spec (CommRingCat.of K) ⟶ S) (x : Over.mk s ⟶ X),
        x ≫ f = x ≫ g) : f = g :=
  EtaleDetection.Construction.etale_ext_of_field_points f g (field_points_eq_of_geometric_points f g h)

/-- The torsion integrality criterion can be tested over algebraically
closed fields, where the isogeny is surjective on points. -/
theorem torsion_vanishing_of_geometric_points
    {S : Scheme.{u}} {B D H : Over S} [GrpObj B] [GrpObj D]
    (n : ℕ) (i : H ⟶ B) (hi : i ^ n = 1)
    (f : B ⟶ D) [IsMonHom f]
    (h_TorsionQuotient : Etale (TorsionQuotient.SubgroupFunctor.torsionScheme D n).hom)
    (h_geo : ∀ (K : Type u) [Field K] [IsAlgClosed K]
      (s : Spec (CommRingCat.of K) ⟶ S) (x : Over.mk s ⟶ H),
        (x ≫ i) ≫ f = 1) : i ≫ f = 1 := by
  apply EtaleDetection.Construction.torsion_vanishing_of_field_points n i hi f h_TorsionQuotient
  intro K hK s x
  have h := field_points_eq_of_geometric_points (i ≫ f) (1 : H ⟶ D)
    (by
      intro L hL hclosed t y
      simpa only [Category.assoc, MonObj.comp_one] using h_geo L t y)
    K s x
  simpa only [Category.assoc, MonObj.comp_one] using h

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Geometric.Points.Construction
