import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.SplitPointSurjectivity
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.GenericComponentSection

/-! # Component Surjectivity -/

namespace OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Evaluated.ComponentSurjectivity.Lifts

noncomputable section

/-! The evaluated component map is onto on generic points by its actual
scheme surjectivity and the constructed finite splitting. The linear
section therefore needs no point-surjectivity hypothesis. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory
open scoped _root_.CategoryTheory.MonObj

universe u

theorem testPoints_surjective_of_pullback {S T : Scheme.{u}} (s : T ⟶ S)
    {X Y : Over S} (f : X ⟶ Y)
    (hs : Function.Surjective (fun a : (𝟙_ (Over T)) ⟶ (Over.pullback s).obj X ↦
      a ≫ (Over.pullback s).map f)) :
    Function.Surjective (fun a : Over.mk s ⟶ X ↦ a ≫ f) := by
  let e : (Over.map s).obj (𝟙_ (Over T)) ≅ Over.mk s :=
    Over.isoMk (Iso.refl T) (by simp)
  let adj := Over.mapPullbackAdj s
  intro b
  obtain ⟨a, ha⟩ := hs (adj.homEquiv _ _ (e.hom ≫ b))
  refine ⟨e.inv ≫ (adj.homEquiv _ _).symm a, ?_⟩
  apply (cancel_epi e.hom).mp
  simp only [← Category.assoc, e.hom_inv_id, Category.id_comp]
  apply (adj.homEquiv _ _).injective
  rw [adj.homEquiv_naturality_right, Equiv.apply_symm_apply]
  exact ha

theorem overPullbackMap_isPullback {S T : Scheme.{u}} (s : T ⟶ S)
    {X Y : Over S} (f : X ⟶ Y) :
    IsPullback ((Over.pullback s).map f).left (Limits.pullback.fst X.hom s)
      (Limits.pullback.fst Y.hom s) f.left := by
  have hr := (IsPullback.of_hasPullback Y.hom s).flip
  have ho : IsPullback (((Over.pullback s).map f).left ≫ Limits.pullback.snd Y.hom s)
      (Limits.pullback.fst X.hom s) s (f.left ≫ Y.hom) := by
    have hs : ((Over.pullback s).map f).left ≫ Limits.pullback.snd Y.hom s =
        Limits.pullback.snd X.hom s := ((Over.pullback s).map f).w
    rw [hs, f.w]
    exact (IsPullback.of_hasPullback X.hom s).flip
  exact IsPullback.of_right ho (Limits.pullback.lift_fst _ _ _) hr

theorem evaluated_component_points_surjective
    (R L : Type u) [CommRing R] [Field L] [Algebra R L]
    {A : Over (Spec (.of R))} {I W : Type u} [Group W]
    (π : A ⟶ (AbelianScheme.FrobeniusKernel.EtaleSubgroups.Construction.etaleGroupScheme (Spec (.of R)) W).X) [Surjective π.left]
    (eA : AbelianModuli.HilbertConstruction.ConstantScheme.Iff.constantScheme (Spec (.of L)) I ≅
      (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R L)))).obj A) :
    Function.Surjective (fun a : Sections.Lifts.genericTest R L ⟶ A ↦ a ≫ π) := by
  let s := Spec.map (CommRingCat.ofHom (algebraMap R L))
  have hsurj : Surjective ((Over.pullback s).map π).left :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (overPullbackMap_isPullback s π).flip (inferInstanceAs (Surjective π.left))
  exact testPoints_surjective_of_pullback s π
    (@SplitPointSurjectivity.Lifts.split_points_surjective L _ I W _ _ eA (AbelianModuli.HilbertConstruction.Constant.BaseChange.constantSchemeBaseChangeIso s W)
      ((Over.pullback s).map π) hsurj)

variable (R L : Type) [CommRing R] [Field L] [Algebra R L]
variable (q : ℕ) [Fact q.Prime]
variable {V W I : Type} [AddCommGroup V] [Module (ZMod q) V]
  [AddCommGroup W] [Module (ZMod q) W]
variable (A : Over (Spec (.of R))) [GrpObj A]
variable (c : (Sections.Lifts.genericTest R L ⟶ A) ≃* Multiplicative V)
variable (π : A ⟶ (AbelianScheme.FrobeniusKernel.EtaleSubgroups.Construction.etaleGroupScheme (Spec (.of R)) (Multiplicative W)).X)
  [IsMonHom π] [Surjective π.left]
variable (eA : AbelianModuli.HilbertConstruction.ConstantScheme.Iff.constantScheme (Spec (.of L)) I ≅
  (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R L)))).obj A)

def constructedGenericSection : W →ₗ[ZMod q] V :=
  GenericComponentSection.Lifts.genericComponentRightInverse R L q A c π (evaluated_component_points_surjective R L π eA)

theorem constructedGenericSection_comp :
    (GenericComponentSection.Lifts.genericComponentLinear R L q A c π).comp (constructedGenericSection R L q A c π eA) =
      LinearMap.id :=
  GenericComponentSection.Lifts.genericComponentRightInverse_comp R L q A c π (evaluated_component_points_surjective R L π eA)

end

end OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Evaluated.ComponentSurjectivity.Lifts
