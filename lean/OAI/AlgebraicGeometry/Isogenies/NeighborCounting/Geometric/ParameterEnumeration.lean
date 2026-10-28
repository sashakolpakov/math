import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Evaluated.ChoiceEnumeration

/-! # Parameter Enumeration -/

namespace OAI.AlgebraicGeometry.Isogenies.NeighborCounting

noncomputable section

/-! The original finite evaluation labels remain an exhaustive,
nonrepeating enumeration after any further field extension. The
geometric points are the base changes of those same original labels. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.CategoryTheory.Limits
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory

universe u

variable {k : Type u} [Field k] {I : Type u} {X : Over (Spec (.of k))}

theorem Geometric.ParameterEnumeration.Lifts.splitLabelPointAt_bijective (e : AbelianModuli.HilbertConstruction.ConstantScheme.Iff.constantScheme (Spec (.of k)) I ≅ X)
    (T : Over (Spec (.of k))) [PreconnectedSpace T.left] (t0 : T.left) :
    Function.Bijective (fun i => toUnit T ≫ SplitPointSurjectivity.Lifts.splitLabelPoint e i) := by
  let c (i : I) : T ⟶ AbelianModuli.HilbertConstruction.ConstantScheme.Iff.constantScheme (Spec (.of k)) I :=
    toUnit T ≫ Over.homMk (Sigma.ι (fun _ : I => Spec (.of k)) i) (AbelianModuli.HilbertConstruction.ConstantScheme.Iff.constantScheme_ι_hom i)
  have hc (i : I) : AbelianModuli.HilbertConstruction.ConstantScheme.Iff.constantSchemePoint T (c i) = LocallyConstant.const _ i := by
    apply LocallyConstant.ext
    intro t
    exact AbelianModuli.HilbertConstruction.ConstantScheme.Iff.constantSchemeIndex_ι i (T.hom t)
  have hp (i : I) : toUnit T ≫ SplitPointSurjectivity.Lifts.splitLabelPoint e i = c i ≫ e.hom :=
    (Category.assoc _ _ _).symm
  constructor
  · intro i j hij
    have h := (cancel_mono e.hom).mp ((hp i).symm.trans (hij.trans (hp j)))
    have hv := congrArg (fun f : T ⟶ AbelianModuli.HilbertConstruction.ConstantScheme.Iff.constantScheme (Spec (.of k)) I => AbelianModuli.HilbertConstruction.ConstantScheme.Iff.constantSchemePoint T f t0) h
    rw [hc, hc] at hv
    exact hv
  · intro a
    let z := a ≫ e.inv
    let i := AbelianModuli.HilbertConstruction.ConstantScheme.Iff.constantSchemePoint T z t0
    have hz : c i = z := by
      apply (AbelianModuli.HilbertConstruction.ConstantScheme.Iff.constantSchemePointsEquiv (Spec (.of k)) I T).injective
      exact (hc i).trans ((AbelianModuli.HilbertConstruction.ConstantScheme.Iff.constantSchemePoint T z).eq_const t0).symm
    refine ⟨i, ?_⟩
    exact (hp i).trans ((congrArg (fun w => w ≫ e.hom) hz).trans
      ((Category.assoc a e.inv e.hom).trans
        ((congrArg (fun w => a ≫ w) e.inv_hom_id).trans (Category.comp_id a))))

def Geometric.ParameterEnumeration.Lifts.splitLabelPointAtEquiv (e : AbelianModuli.HilbertConstruction.ConstantScheme.Iff.constantScheme (Spec (.of k)) I ≅ X)
    (T : Over (Spec (.of k))) [PreconnectedSpace T.left] (t0 : T.left) : I ≃ (T ⟶ X) :=
  Equiv.ofBijective (fun i => toUnit T ≫ SplitPointSurjectivity.Lifts.splitLabelPoint e i) (Geometric.ParameterEnumeration.Lifts.splitLabelPointAt_bijective e T t0)

variable {K : Type u} [Field K] {X : Over (Spec (.of K))}
variable (d : Evaluated.ParameterPoints.Lifts.FiniteEvaluationField K X)
variable (L : Type u) [Field L] (φ : d.carrier →+* L)

abbrev Evaluated.ParameterPoints.Lifts.FiniteEvaluationField.extendedParameterBase : Over (Spec (.of K)) :=
  (Over.map (Spec.map (CommRingCat.ofHom (algebraMap K d.carrier)))).obj
    (Over.mk (Spec.map (CommRingCat.ofHom φ)))

def Evaluated.ParameterPoints.Lifts.FiniteEvaluationField.extendedParameterPointEquiv : ULift.{u} (Fin d.count) ≃ (d.extendedParameterBase L φ ⟶ X) := by
  have : PreconnectedSpace (Over.mk (Spec.map (CommRingCat.ofHom φ))).left :=
    inferInstanceAs (PreconnectedSpace (Spec (.of L)))
  exact (Geometric.ParameterEnumeration.Lifts.splitLabelPointAtEquiv d.parameterIso (Over.mk (Spec.map (CommRingCat.ofHom φ)))
    (IsLocalRing.closedPoint L)).trans
      ((Over.mapPullbackAdj (Spec.map (CommRingCat.ofHom (algebraMap K d.carrier)))).homEquiv
        (Over.mk (Spec.map (CommRingCat.ofHom φ))) X).symm

theorem Evaluated.ParameterPoints.Lifts.FiniteEvaluationField.extendedParameterPointEquiv_left (i : ULift.{u} (Fin d.count)) :
    (d.extendedParameterPointEquiv L φ i).left = Spec.map (CommRingCat.ofHom φ) ≫ d.parameterPoint i := by
  change (Spec.map (CommRingCat.ofHom φ) ≫ (d.labelPoint i).left) ≫
      pullback.fst X.hom (Spec.map (CommRingCat.ofHom (algebraMap K d.carrier))) = _
  exact Category.assoc _ _ _

def Evaluated.ParameterPoints.Lifts.FiniteEvaluationField.parameterExtensionMap : d.extendedParameterBase L φ ⟶
    Over.mk (Spec.map (CommRingCat.ofHom (algebraMap K d.carrier))) :=
  Over.homMk (Spec.map (CommRingCat.ofHom φ)) rfl

theorem Evaluated.ParameterPoints.Lifts.FiniteEvaluationField.extendedParameterPointEquiv_natural (i : ULift.{u} (Fin d.count)) :
    d.extendedParameterPointEquiv L φ i = d.parameterExtensionMap L φ ≫ d.parameterPointEquiv i := by
  apply Over.OverMorphism.ext
  exact (d.extendedParameterPointEquiv_left L φ i).trans
    (congrArg (fun w => Spec.map (CommRingCat.ofHom φ) ≫ w) (d.parameterPointEquiv_left i).symm)

variable (F : (Over (Spec (.of K)))ᵒᵖ ⥤ Type (u + 1)) (repr : F.RepresentableBy X)

def Evaluated.ParameterPoints.Lifts.FiniteEvaluationField.extendedChoiceEquiv : ULift.{u} (Fin d.count) ≃ F.obj (.op (d.extendedParameterBase L φ)) :=
  (d.extendedParameterPointEquiv L φ).trans repr.homEquiv

theorem Evaluated.ParameterPoints.Lifts.FiniteEvaluationField.extendedChoiceEquiv_natural (i : ULift.{u} (Fin d.count)) :
    d.extendedChoiceEquiv L φ F repr i =
      F.map (d.parameterExtensionMap L φ).op (d.evaluatedChoiceEquiv F repr i) := by
  change repr.homEquiv (d.extendedParameterPointEquiv L φ i) = _
  rw [Evaluated.ParameterPoints.Lifts.FiniteEvaluationField.extendedParameterPointEquiv_natural]
  exact repr.homEquiv_comp _ _

end

end OAI.AlgebraicGeometry.Isogenies.NeighborCounting
