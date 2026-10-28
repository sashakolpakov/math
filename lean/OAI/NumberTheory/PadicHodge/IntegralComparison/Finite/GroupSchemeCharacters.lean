import OAI.AlgebraicGeometry.FormalGeometry.Completion.TorsionPointAction

/-! # Group Scheme Characters -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Finite.GroupSchemeCharacters

noncomputable section

/-! Characters of the actual field points of a finite group scheme over
an algebraically closed field are continuous functions on its underlying
space. Their addition law holds after arbitrary scheme pullback. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open MonoidalCategory CartesianMonoidalCategory MonObj

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u w
variable {k : Type u} [Field k] [IsAlgClosed k]
  (T : Over (Spec (.of k))) [IsFinite T.hom]

omit [IsAlgClosed k] in
theorem finite_space : Finite T.left := by
  apply Set.finite_univ_iff.mp
  exact (T.hom.finite_preimage_singleton (IsLocalRing.closedPoint k)).subset
    (fun _ _ => Subsingleton.elim _ _)

omit [IsAlgClosed k] in
theorem discrete_space : DiscreteTopology T.left := by
  let : Finite T.left := finite_space T
  let : JacobsonSpace T.left := LocallyOfFiniteType.jacobsonSpace T.hom
  exact JacobsonSpace.discreteTopology (Set.toFinite (closedPoints T.left))

def pointEquiv : (𝟙_ (Over (Spec (.of k))) ⟶ T) ≃ T.left :=
  Equiv.ofBijective (fun f => f.left (IsLocalRing.closedPoint k)) (by
    constructor
    · intro f g h
      apply Over.OverMorphism.ext
      exact ext_of_apply_closedPoint_eq T.hom f.w g.w h
    · intro z
      let : DiscreteTopology T.left := discrete_space T
      exact ⟨Over.homMk (pointOfClosedPoint T.hom z isClosed_singleton)
        (pointOfClosedPoint_comp T.hom z isClosed_singleton),
        pointOfClosedPoint_apply T.hom z isClosed_singleton _⟩)

variable {M : Type w} [TopologicalSpace M]

def continuousFunction (f : (𝟙_ (Over (Spec (.of k))) ⟶ T) → M) : C(T.left, M) := by
  let : DiscreteTopology T.left := discrete_space T
  exact ⟨fun z => f ((pointEquiv T).symm z), continuous_of_discreteTopology⟩

@[simp] theorem continuousFunction_point
    (f : (𝟙_ (Over (Spec (.of k))) ⟶ T) → M) (s : 𝟙_ (Over (Spec (.of k))) ⟶ T) :
    continuousFunction T f (s.left (IsLocalRing.closedPoint k)) = f s :=
  congrArg f ((pointEquiv T).symm_apply_apply s)

variable [GrpObj T] [AddCommGroup M]

theorem multiplication_value (χ : Additive (𝟙_ (Over (Spec (.of k))) ⟶ T) →+ M)
    (z : (T ⊗ T).left) :
    continuousFunction T (fun t => χ (Additive.ofMul t)) (μ[T].left z) =
      continuousFunction T (fun t => χ (Additive.ofMul t)) ((fst T T).left z) +
        continuousFunction T (fun t => χ (Additive.ofMul t)) ((snd T T).left z) := by
  let : IsFinite (T ⊗ T).hom := by
    change IsFinite (pullback.fst T.hom T.hom ≫ T.hom)
    infer_instance
  obtain ⟨s, hs⟩ := (pointEquiv (T ⊗ T)).surjective z
  change s.left (IsLocalRing.closedPoint k) = z at hs
  subst z
  have hv (f : T ⊗ T ⟶ T) : f.left (s.left (IsLocalRing.closedPoint k)) =
      (s ≫ f).left (IsLocalRing.closedPoint k) := rfl
  simp only [hv, continuousFunction_point]
  have he : s ≫ μ[T] = (s ≫ fst T T) * (s ≫ snd T T) := by
    rw [← MonObj.comp_mul, MonObj.mul_eq_mul]
  rw [he]
  exact χ.map_add _ _

theorem pullback_mul (χ : Additive (𝟙_ (Over (Spec (.of k))) ⟶ T) →+ M)
    {W : Over (Spec (.of k))} (f g : W ⟶ T) (z : W.left) :
    continuousFunction T (fun t => χ (Additive.ofMul t)) ((f * g).left z) =
      continuousFunction T (fun t => χ (Additive.ofMul t)) (f.left z) +
        continuousFunction T (fun t => χ (Additive.ofMul t)) (g.left z) := by
  have h := multiplication_value T χ ((lift f g).left z)
  have hm : lift f g ≫ μ[T] = f * g := rfl
  have ha := congrArg (fun a : W ⟶ T => a.left z) (lift_fst f g)
  have hb := congrArg (fun a : W ⟶ T => a.left z) (lift_snd f g)
  have hm' := congrArg (fun a : W ⟶ T => a.left z) hm
  change μ[T].left ((lift f g).left z) = (f * g).left z at hm'
  change (fst T T).left ((lift f g).left z) = f.left z at ha
  change (snd T T).left ((lift f g).left z) = g.left z at hb
  rw [hm', ha, hb] at h
  exact h

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Finite.GroupSchemeCharacters
