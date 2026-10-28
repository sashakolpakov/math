import OAI.ArithmeticGeometry.Models.SpreadingOut.OpenOver
import OAI.ArithmeticGeometry.Models.SpreadingOut.DenseChartFactor
import OAI.ArithmeticGeometry.Models.SpreadingOut.ClosedProjection
import OAI.ArithmeticGeometry.Models.SpreadingOut.RestrictedGraph

/-! # Chow Chart -/

namespace OAI.ArithmeticGeometry.Models.SpreadingOut.ChowChart.Construction

noncomputable section

/-! The local chart comparison in the graph construction of a projective cover. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u

/-- An extension of one coordinate map on an open source chart forces that
part of a reduced graph closure to stay in the corresponding target chart. -/
theorem dense_chart_extension_preimage_le
    {S : Scheme.{u}} {W Z X Q : Over S}
    [IsReduced Z.left] [IsSeparated Q.hom]
    (d : W ⟶ Z) [IsDominant d.left] (p : Z ⟶ X) (q : Z ⟶ Q)
    (V : X.left.Opens) (A : Q.left.Opens)
    (k : W ⟶ OpenOver.Construction.overOpen X V) (e : OpenOver.Construction.overOpen X V ⟶ OpenOver.Construction.overOpen Q A)
    (hp : d ≫ p = k ≫ OpenOver.Construction.overOpenInclusion X V)
    (hq : d ≫ q = k ≫ e ≫ OpenOver.Construction.overOpenInclusion Q A) :
    p.left ⁻¹ᵁ V ≤ q.left ⁻¹ᵁ A := by
  have hr : Set.range (d ≫ p).left ⊆ (V : Set X.left) :=
    OpenOver.Construction.range_subset_of_overOpen_factor (d ≫ p) V k hp.symm
  have hd : Set.range d.left ⊆ (p.left ⁻¹ᵁ V : Set Z.left) := by
    rintro _ ⟨x, rfl⟩
    exact hr (Set.mem_range_self x)
  let D := OpenOver.Construction.overOpen Z (p.left ⁻¹ᵁ V)
  let d₀ := OpenOver.Construction.overOpenLift d (p.left ⁻¹ᵁ V) hd
  have : IsDominant d₀.left := OpenOver.Construction.overOpenLift_dominant d _ hd
  let p₀ := OpenOver.Construction.overOpenRestrict p V
  have hdp : d₀ ≫ p₀ = k := by
    apply (cancel_mono (OpenOver.Construction.overOpenInclusion X V)).mp
    dsimp only [p₀]
    rw [Category.assoc, OpenOver.Construction.overOpenRestrict_inclusion, ← Category.assoc,
      OpenOver.Construction.overOpenLift_inclusion]
    exact hp
  let a : D ⟶ Q := p₀ ≫ e ≫ OpenOver.Construction.overOpenInclusion Q A
  let b : D ⟶ Q := OpenOver.Construction.overOpenInclusion Z (p.left ⁻¹ᵁ V) ≫ q
  have hab : a = b := by
    apply OpenOver.Construction.over_hom_ext_of_dominant d₀
    change d₀ ≫ (p₀ ≫ e ≫ OpenOver.Construction.overOpenInclusion Q A) =
      d₀ ≫ (OpenOver.Construction.overOpenInclusion Z (p.left ⁻¹ᵁ V) ≫ q)
    rw [← Category.assoc d₀ p₀ (e ≫ OpenOver.Construction.overOpenInclusion Q A), hdp]
    simpa only [d₀, OpenOver.Construction.overOpenLift_inclusion_assoc] using hq.symm
  intro z hz
  let z₀ : D.left := ⟨z, hz⟩
  have heq : a.left z₀ = b.left z₀ := congrArg (fun f : D ⟶ Q ↦ f.left z₀) hab
  change b.left z₀ ∈ A
  rw [← heq]
  exact ((p₀ ≫ e).left z₀).property

theorem dense_chart_closed_restriction
    {S : Scheme.{u}} {W Z X P Q : Over S}
    [IsReduced Z.left] [IsSeparated X.hom]
    (d : W ⟶ Z) [IsDominant d.left] (p : Z ⟶ X) (q : Z ⟶ P)
    [IsClosedImmersion (pullback.lift p.left q.left (p.w.trans q.w.symm))]
    (π : P ⟶ Q) (V : X.left.Opens) (A : Q.left.Opens)
    (k : W ⟶ OpenOver.Construction.overOpen X V) (e : OpenOver.Construction.overOpen X V ⟶ OpenOver.Construction.overOpen Q A)
    [IsClosedImmersion e.left]
    (hp : d ≫ p = k ≫ OpenOver.Construction.overOpenInclusion X V)
    (hq : d ≫ q ≫ π = k ≫ e ≫ OpenOver.Construction.overOpenInclusion Q A) :
    IsClosedImmersion (q.left ∣_ (π.left ⁻¹ᵁ A)) := by
  let B := π.left ⁻¹ᵁ A
  let D := q.left ⁻¹ᵁ B
  have hr : Set.range (d ≫ q ≫ π).left ⊆ (A : Set Q.left) :=
    OpenOver.Construction.range_subset_of_overOpen_factor (d ≫ q ≫ π) A (k ≫ e)
      ((Category.assoc _ _ _).trans hq.symm)
  have hd : Set.range d.left ⊆ (D : Set Z.left) := by
    rintro _ ⟨x, rfl⟩
    exact hr (Set.mem_range_self x)
  let d₀ := OpenOver.Construction.overOpenLift d D hd
  have : IsDominant d₀.left := OpenOver.Construction.overOpenLift_dominant d D hd
  let p₀ : OpenOver.Construction.overOpen Z D ⟶ X := OpenOver.Construction.overOpenInclusion Z D ≫ p
  let q₀ := OpenOver.Construction.overOpenRestrict q B
  let r₀ := OpenOver.Construction.overOpenRestrict π A
  have hdp : d₀ ≫ p₀ = k ≫ OpenOver.Construction.overOpenInclusion X V := by
    change d₀ ≫ (OpenOver.Construction.overOpenInclusion Z D ≫ p) = _
    rw [← Category.assoc, OpenOver.Construction.overOpenLift_inclusion]
    exact hp
  have hdq : d₀ ≫ q₀ ≫ r₀ = k ≫ e := by
    apply (cancel_mono (OpenOver.Construction.overOpenInclusion Q A)).mp
    simpa only [d₀, q₀, r₀, D, B, Category.assoc, OpenOver.Construction.overOpenRestrict_inclusion,
      OpenOver.Construction.overOpenRestrict_inclusion_assoc, OpenOver.Construction.overOpenLift_inclusion_assoc] using hq
  obtain ⟨l, hlp, hle⟩ := DenseChartFactor.Construction.factor_through_chart_of_dense d₀ (OpenOver.Construction.overOpenInclusion X V) e
    p₀ (q₀ ≫ r₀) k (congrArg (fun f ↦ f.left) hdp) (congrArg (fun f ↦ f.left) hdq)
  have : IsClosedImmersion (pullback.lift p₀.left q₀.left (p₀.w.trans q₀.w.symm)) :=
    RestrictedGraph.Construction.restricted_graph_closedImmersion p q B _
  exact ClosedProjection.Construction.closed_projection_of_chart_factor p₀ q₀ (OpenOver.Construction.overOpenInclusion X V) e r₀ l hlp hle

end

end OAI.ArithmeticGeometry.Models.SpreadingOut.ChowChart.Construction
