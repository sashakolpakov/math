import OAI.ArithmeticGeometry.Descent.CMVariety.EmbeddedGroupCoefficients
import Mathlib.AlgebraicGeometry.Group.Smooth

/-! # Open Group Generation -/

namespace OAI.ArithmeticGeometry.Descent.CMVariety.OpenGroupGeneration.Abelian

noncomputable section

/-! A nonempty open in an irreducible smooth group over an algebraically
closed field generates the whole group by products of two points. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

def fieldPointLiftToOpen {K : Type} [Field K] {V G : Over (Spec (.of K))}
    (i : V ⟶ G) [IsOpenImmersion i.left] (p : 𝟙_ (Over (Spec (.of K))) ⟶ G)
    (hp : p.left (IsLocalRing.closedPoint K) ∈ Set.range i.left) :
    𝟙_ (Over (Spec (.of K))) ⟶ V := by
  have hr : Set.range p.left ⊆ Set.range i.left := by
    rintro _ ⟨x, rfl⟩
    have hx : x = IsLocalRing.closedPoint K := @Subsingleton.elim (PrimeSpectrum K) _ x _
    rwa [hx]
  let q := IsOpenImmersion.lift i.left p.left hr
  exact Over.homMk q (by
    rw [← i.w, ← Category.assoc, IsOpenImmersion.lift_fac]
    exact p.w)

theorem fieldPointLiftToOpen_comp {K : Type} [Field K] {V G : Over (Spec (.of K))}
    (i : V ⟶ G) [IsOpenImmersion i.left] (p : 𝟙_ (Over (Spec (.of K))) ⟶ G)
    (hp : p.left (IsLocalRing.closedPoint K) ∈ Set.range i.left) :
    fieldPointLiftToOpen i p hp ≫ i = p := by
  apply Over.OverMorphism.ext
  exact IsOpenImmersion.lift_fac _ _ _

theorem open_group_product_surjective
    {K : Type} [Field K] [IsAlgClosed K] {V G : Over (Spec (.of K))}
    [GrpObj G] [Smooth G.hom] [IrreducibleSpace G.left] [Nonempty V.left]
    (i : V ⟶ G) [IsOpenImmersion i.left] : Surjective (EmbeddedGroupCoefficients.Abelian.groupOpenProduct i).left := by
  have : JacobsonSpace G.left := LocallyOfFiniteType.jacobsonSpace G.hom
  have : Smooth (EmbeddedGroupCoefficients.Abelian.groupOpenProduct i).left := EmbeddedGroupCoefficients.Abelian.groupOpenProduct_smooth i
  have hclosed : ∀ z : G.left, IsClosed {z} → z ∈ Set.range (EmbeddedGroupCoefficients.Abelian.groupOpenProduct i).left := by
    intro z hz
    let z' : 𝟙_ (Over (Spec (.of K))) ⟶ G :=
      Over.homMk (pointOfClosedPoint G.hom z hz) (pointOfClosedPoint_comp G.hom z hz)
    let e : G ≅ G := asIso (GrpObj.inv (X := G)) ≪≫ GrpObj.mulRight z'
    have : IsIso e.hom.left := ((Over.forget (Spec (.of K))).mapIso e).isIso_hom
    let U := Set.range i.left
    have hU : IsOpen U := i.left.isOpenEmbedding.isOpen_range
    have hUne : U.Nonempty := Set.range_nonempty i.left
    have hpre : (e.hom.left ⁻¹' U).Nonempty := by
      obtain ⟨w, hw⟩ := hUne
      obtain ⟨v, hv⟩ := e.hom.left.surjective w
      exact ⟨v, by change e.hom.left v ∈ U; rwa [hv]⟩
    have hinter := nonempty_preirreducible_inter hU (hU.preimage e.hom.left.continuous) hUne hpre
    obtain ⟨b, ⟨hbU, hbeU⟩, hbc⟩ := nonempty_inter_closedPoints hinter
      (hU.inter (hU.preimage e.hom.left.continuous)).isLocallyClosed
    let b' : 𝟙_ (Over (Spec (.of K))) ⟶ G :=
      Over.homMk (pointOfClosedPoint G.hom b hbc) (pointOfClosedPoint_comp G.hom b hbc)
    have hb' : b'.left (IsLocalRing.closedPoint K) = b := pointOfClosedPoint_apply G.hom b hbc _
    have hbLift : b'.left (IsLocalRing.closedPoint K) ∈ Set.range i.left := hb'.symm ▸ hbU
    have hcLift : (b' ≫ e.hom).left (IsLocalRing.closedPoint K) ∈ Set.range i.left := by
      change e.hom.left (b'.left (IsLocalRing.closedPoint K)) ∈ U
      rwa [hb']
    let a := fieldPointLiftToOpen i b' hbLift
    let c := fieldPointLiftToOpen i (b' ≫ e.hom) hcLift
    have ha : a ≫ i = b' := fieldPointLiftToOpen_comp i b' hbLift
    have hc : c ≫ i = b' ≫ e.hom := fieldPointLiftToOpen_comp i (b' ≫ e.hom) hcLift
    have hp : lift a c ≫ EmbeddedGroupCoefficients.Abelian.groupOpenProduct i = z' := by
      rw [EmbeddedGroupCoefficients.Abelian.groupOpenProduct_points, ha, hc]
      simp [e, GrpObj.mulRight, ← Hom.mul_def, MonObj.comp_mul, ← Hom.inv_def]
    refine ⟨(lift a c).left (IsLocalRing.closedPoint K), ?_⟩
    have h := congrArg (fun p : 𝟙_ (Over (Spec (.of K))) ⟶ G =>
      p.left (IsLocalRing.closedPoint K)) hp
    exact h.trans (pointOfClosedPoint_apply G.hom z hz _)
  constructor
  intro x
  by_contra hx
  obtain ⟨z, hz, hzc⟩ := nonempty_inter_closedPoints
    (Z := (Set.range (EmbeddedGroupCoefficients.Abelian.groupOpenProduct i).left)ᶜ) ⟨x, hx⟩
    (EmbeddedGroupCoefficients.Abelian.groupOpenProduct i).left.isOpenMap.isOpen_range.isClosed_compl.isLocallyClosed
  exact hz (hclosed z hzc)

end

end OAI.ArithmeticGeometry.Descent.CMVariety.OpenGroupGeneration.Abelian
