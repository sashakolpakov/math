import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.SplitPointSurjectivity

/-! # Enumeration -/

namespace OAI.AlgebraicGeometry.Isogenies.NeighborCounting

noncomputable section

/-! The constructed finite evaluation labels enumerate every point of
the original parameter scheme over the evaluation field exactly once. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.CategoryTheory.Limits
open _root_.CategoryTheory.MonoidalCategory

universe u

variable {k : Type u} [Field k] {I : Type u}

theorem Parameter.Enumeration.Lifts.splitLabelPoint_bijective {X : Over (Spec (.of k))}
    (e : AbelianModuli.HilbertConstruction.ConstantScheme.Iff.constantScheme (Spec (.of k)) I ≅ X) : Function.Bijective (SplitPointSurjectivity.Lifts.splitLabelPoint e) := by
  let T : Over (Spec (.of k)) := Over.mk (𝟙 _)
  have : PreconnectedSpace T.left := inferInstanceAs (PreconnectedSpace (Spec (.of k)))
  let c (i : I) : T ⟶ AbelianModuli.HilbertConstruction.ConstantScheme.Iff.constantScheme (Spec (.of k)) I :=
    Over.homMk (Sigma.ι (fun _ : I ↦ Spec (.of k)) i) (AbelianModuli.HilbertConstruction.ConstantScheme.Iff.constantScheme_ι_hom i)
  have hc (i : I) : AbelianModuli.HilbertConstruction.ConstantScheme.Iff.constantSchemePoint T (c i) = LocallyConstant.const _ i := by
    apply LocallyConstant.ext
    exact AbelianModuli.HilbertConstruction.ConstantScheme.Iff.constantSchemeIndex_ι i
  constructor
  · intro i j hij
    have he : c i = c j := (cancel_mono e.hom).mp hij
    have h := congrArg (fun f : T ⟶ AbelianModuli.HilbertConstruction.ConstantScheme.Iff.constantScheme (Spec (.of k)) I =>
      AbelianModuli.HilbertConstruction.ConstantScheme.Iff.constantSchemePoint T f (IsLocalRing.closedPoint k)) he
    rw [hc, hc] at h
    exact h
  · intro a
    let z : T ⟶ AbelianModuli.HilbertConstruction.ConstantScheme.Iff.constantScheme (Spec (.of k)) I := a ≫ e.inv
    let i := AbelianModuli.HilbertConstruction.ConstantScheme.Iff.constantSchemePoint T z (IsLocalRing.closedPoint k)
    have hz : c i = z := by
      apply (AbelianModuli.HilbertConstruction.ConstantScheme.Iff.constantSchemePointsEquiv (Spec (.of k)) I T).injective
      exact (hc i).trans ((AbelianModuli.HilbertConstruction.ConstantScheme.Iff.constantSchemePoint T z).eq_const (IsLocalRing.closedPoint k)).symm
    refine ⟨i, ?_⟩
    change c i ≫ e.hom = a
    rw [hz]
    change (a ≫ e.inv) ≫ e.hom = a
    rw [Category.assoc, e.inv_hom_id, Category.comp_id]

def Parameter.Enumeration.Lifts.splitLabelPointEquiv {X : Over (Spec (.of k))}
    (e : AbelianModuli.HilbertConstruction.ConstantScheme.Iff.constantScheme (Spec (.of k)) I ≅ X) :
    I ≃ (𝟙_ (Over (Spec (.of k))) ⟶ X) :=
  Equiv.ofBijective (SplitPointSurjectivity.Lifts.splitLabelPoint e) (Parameter.Enumeration.Lifts.splitLabelPoint_bijective e)

/-- The point/section comparison uses the actual scheme pullback. -/
def Parameter.Enumeration.Lifts.parameterPullbackPointEquiv {S T : Scheme.{u}} (s : T ⟶ S) (X : Over S) :
    (Over.mk (𝟙 T) ⟶ (Over.pullback s).obj X) ≃ (Over.mk s ⟶ X) where
  toFun a := Over.homMk (a.left ≫ pullback.fst X.hom s) (by
    have h : a.left ≫ pullback.snd X.hom s = 𝟙 T := a.w
    rw [Category.assoc, pullback.condition, ← Category.assoc, h]
    exact Category.id_comp s)
  invFun a := Over.homMk (pullback.lift a.left (𝟙 T)
    (a.w.trans (Category.id_comp s).symm)) (pullback.lift_snd _ _ _)
  left_inv a := by
    apply Over.OverMorphism.ext
    apply pullback.hom_ext
    · exact pullback.lift_fst _ _ _
    · exact (pullback.lift_snd _ _ _).trans a.w.symm
  right_inv a := by
    apply Over.OverMorphism.ext
    exact pullback.lift_fst _ _ _

variable {K : Type u} [Field K] {X : Over (Spec (.of K))}
variable (d : Evaluated.ParameterPoints.Lifts.FiniteEvaluationField K X)

def Evaluated.ParameterPoints.Lifts.FiniteEvaluationField.parameterPointEquiv : ULift.{u} (Fin d.count) ≃
    (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap K d.carrier))) ⟶ X) :=
  (Parameter.Enumeration.Lifts.splitLabelPointEquiv d.parameterIso).trans
    (Parameter.Enumeration.Lifts.parameterPullbackPointEquiv (Spec.map (CommRingCat.ofHom (algebraMap K d.carrier))) X)

theorem Evaluated.ParameterPoints.Lifts.FiniteEvaluationField.parameterPointEquiv_left (i : ULift.{u} (Fin d.count)) :
    (d.parameterPointEquiv i).left = d.parameterPoint i := rfl

/-- Every actual evaluated parameter appears once; the target map may
still identify different parameters, preserving their multiplicity. -/
theorem Evaluated.ParameterPoints.Lifts.FiniteEvaluationField.parameterPoint_complete
    (a : Spec (.of d.carrier) ⟶ X.left)
    (ha : a ≫ X.hom = Spec.map (CommRingCat.ofHom (algebraMap K d.carrier))) :
    ∃! i, d.parameterPoint i = a := by
  obtain ⟨i, hi⟩ := d.parameterPointEquiv.surjective (Over.homMk a ha)
  refine ⟨i, congrArg Over.Hom.left hi, ?_⟩
  intro j hj
  apply d.parameterPointEquiv.injective
  apply Over.OverMorphism.ext
  exact hj.trans (congrArg Over.Hom.left hi).symm

end

end OAI.AlgebraicGeometry.Isogenies.NeighborCounting
