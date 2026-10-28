import OAI.AlgebraicGeometry.Resolution.Blowups.HypersurfaceChart
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import OAI.AlgebraicGeometry.Resolution.Blowups.PolynomialTranslation

/-! # Polynomial Etale -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.PolynomialEtale.Construction

noncomputable section

section

/-! Étale charts obtained by inverting a full presentation Jacobian. -/

open _root_.Algebra _root_.MvPolynomial

/-- A finite presentation of relative dimension zero becomes étale after
localizing at its selected full Jacobian. -/
theorem preSubmersive_etale_of_localization
    {R S ι σ : Type*} [CommRing R] [CommRing S] [Algebra R S] [Finite ι] [Finite σ]
    (P : PreSubmersivePresentation R S ι σ) (hP : P.dimension = 0)
    (L : Type*) [CommRing L] [Algebra S L] [Algebra R L] [IsScalarTower R S L]
    [IsLocalization.Away P.jacobian L] : Algebra.Etale R L := by
  let Q : PreSubmersivePresentation S L Unit Unit :=
    PreSubmersivePresentation.localizationAway L P.jacobian
  have hu : IsUnit (algebraMap S L P.jacobian) :=
    IsLocalization.Away.algebraMap_isUnit P.jacobian
  let P' : SubmersivePresentation R L (Unit ⊕ ι) (Unit ⊕ σ) :=
    { toPreSubmersivePresentation := Q.comp P
      jacobian_isUnit := by
        rw [PreSubmersivePresentation.comp_jacobian_eq_jacobian_smul_jacobian]
        rw [Algebra.smul_def, PreSubmersivePresentation.localizationAway_jacobian]
        exact hu.mul hu }
  have hdim : P'.dimension = 0 := by
    change (Q.comp P).dimension = 0
    rw [PreSubmersivePresentation.dimension_comp_eq_dimension_add_dimension, hP]
    simp [Presentation.dimension]
  let : IsStandardSmoothOfRelativeDimension 0 R L := P'.isStandardSmoothOfRelativeDimension hdim
  infer_instance

/-- A single polynomial equation in one variable defines an étale algebra
on the open set where its derivative is invertible. -/
theorem oneVariable_hypersurfaceDerivativeChart_etale
    {R : Type*} [CommRing R] (q : MvPolynomial Unit R) :
    Algebra.Etale R (HypersurfaceChart.Construction.hypersurfaceDerivativeChart q ()) := by
  let P := HypersurfaceChart.Construction.hypersurfacePreSubmersive q ()
  let : IsLocalization.Away P.jacobian (HypersurfaceChart.Construction.hypersurfaceDerivativeChart q ()) := by
    rw [HypersurfaceChart.Construction.hypersurfacePreSubmersive_jacobian]
    infer_instance
  apply preSubmersive_etale_of_localization P
  simp [Presentation.dimension]

/-- The corresponding map of actual affine schemes is étale. -/
theorem oneVariable_hypersurfaceDerivativeChart_scheme_etale
    {R : Type*} [CommRing R] (q : MvPolynomial Unit R) :
    AlgebraicGeometry.Etale
      (AlgebraicGeometry.Spec.map (CommRingCat.ofHom
        (algebraMap R (HypersurfaceChart.Construction.hypersurfaceDerivativeChart q ())))) := by
  let : Algebra.Etale R (HypersurfaceChart.Construction.hypersurfaceDerivativeChart q ()) :=
    oneVariable_hypersurfaceDerivativeChart_etale q
  rw [AlgebraicGeometry.HasRingHomProperty.Spec_iff (P := @AlgebraicGeometry.Etale)]
  exact (RingHom.etale_algebraMap (R := R) (S := HypersurfaceChart.Construction.hypersurfaceDerivativeChart q ())).mpr inferInstance

end

section

/-! A graph presentation for changing a polynomial coordinate étale locally. -/

open _root_.Polynomial _root_.CategoryTheory

variable {R : Type*} [CommRing R]

/-- View a polynomial in the graph's extra variable, retaining its coefficients. -/
def graphPolynomialLift : R[X] →+* MvPolynomial Unit R[X] :=
  eval₂RingHom (MvPolynomial.C.comp C) (MvPolynomial.X ())

/-- The graph equation `y = p(x)`, with `y` in the coefficient ring. -/
def graphPolynomialRelation (p : R[X]) : MvPolynomial Unit R[X] :=
  MvPolynomial.C X - graphPolynomialLift p

abbrev polynomialGraphRing (p : R[X]) := HypersurfaceChart.Construction.hypersurfaceRing (graphPolynomialRelation p)

/-- Substitute `p(x)` for the graph's coefficient variable. -/
def graphEvaluation (p : R[X]) : MvPolynomial Unit R[X] →+* R[X] :=
  MvPolynomial.eval₂Hom (compRingHom p) (fun _ => X)

theorem graphEvaluation_lift (p : R[X]) :
    (graphEvaluation p).comp graphPolynomialLift = RingHom.id R[X] := by
  apply Polynomial.ringHom_ext
  · intro r
    simp [graphEvaluation, graphPolynomialLift]
  · simp [graphEvaluation, graphPolynomialLift]

theorem graphEvaluation_relation (p : R[X]) : graphEvaluation p (graphPolynomialRelation p) = 0 := by
  rw [graphPolynomialRelation, map_sub]
  have he := congrArg (fun f : R[X] →+* R[X] => f p) (graphEvaluation_lift p)
  change (graphEvaluation p) (MvPolynomial.C X) - (graphEvaluation p) (graphPolynomialLift p) = 0
  rw [show graphEvaluation p (graphPolynomialLift p) = p from he]
  simp [graphEvaluation]

/-- Eliminate the graph equation to recover the original polynomial ring. -/
def polynomialGraphToPolynomial (p : R[X]) : polynomialGraphRing p →+* R[X] :=
  Ideal.Quotient.lift (Ideal.span {graphPolynomialRelation p}) (graphEvaluation p) (by
    change Ideal.span {graphPolynomialRelation p} ≤ RingHom.ker (graphEvaluation p)
    apply Ideal.span_le.mpr
    rintro r (rfl : r = graphPolynomialRelation p)
    exact graphEvaluation_relation p)

theorem polynomialGraphToPolynomial_mk (p : R[X]) (q : MvPolynomial Unit R[X]) :
    polynomialGraphToPolynomial p (Ideal.Quotient.mk (Ideal.span {graphPolynomialRelation p}) q) =
      graphEvaluation p q := rfl

/-- Include the original variable as the extra variable in the graph ring. -/
def polynomialToGraph (p : R[X]) : R[X] →+* polynomialGraphRing p :=
  (Ideal.Quotient.mk (Ideal.span {graphPolynomialRelation p})).comp graphPolynomialLift

theorem polynomialGraph_relation (p : R[X]) :
    polynomialToGraph p p =
      Ideal.Quotient.mk (Ideal.span {graphPolynomialRelation p}) (MvPolynomial.C X) := by
  have h := Ideal.Quotient.eq_zero_iff_mem.mpr
    (Ideal.subset_span (Set.mem_singleton (graphPolynomialRelation p)))
  change Ideal.Quotient.mk (Ideal.span {graphPolynomialRelation p}) (graphPolynomialRelation p) = 0 at h
  rw [graphPolynomialRelation, map_sub, sub_eq_zero] at h
  exact h.symm

theorem polynomialToGraph_comp_substitution (p : R[X]) :
    (polynomialToGraph p).comp (compRingHom p) =
      (Ideal.Quotient.mk (Ideal.span {graphPolynomialRelation p})).comp MvPolynomial.C := by
  apply Polynomial.ringHom_ext
  · intro r
    simp [polynomialToGraph, graphPolynomialLift]
  · rw [RingHom.comp_apply, coe_compRingHom_apply, X_comp]
    exact polynomialGraph_relation p

theorem polynomialGraph_left_inverse (p : R[X]) :
    (polynomialToGraph p).comp (polynomialGraphToPolynomial p) = RingHom.id _ := by
  apply Ideal.Quotient.ringHom_ext
  apply MvPolynomial.ringHom_ext
  · intro r
    change polynomialToGraph p (graphEvaluation p (MvPolynomial.C r)) =
      Ideal.Quotient.mk (Ideal.span {graphPolynomialRelation p}) (MvPolynomial.C r)
    have h := congrArg (fun f : R[X] →+* polynomialGraphRing p => f r)
      (polynomialToGraph_comp_substitution p)
    simpa only [graphEvaluation, MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_C,
      RingHom.comp_apply] using h
  · intro i
    cases i
    simp [polynomialGraphToPolynomial, polynomialToGraph, graphEvaluation, graphPolynomialLift]

theorem polynomialGraph_right_inverse (p : R[X]) :
    (polynomialGraphToPolynomial p).comp (polynomialToGraph p) = RingHom.id _ := by
  apply RingHom.ext
  intro q
  exact congrArg (fun f : R[X] →+* R[X] => f q) (graphEvaluation_lift p)

/-- The graph presentation is an actual ring isomorphism with the ambient
polynomial ring; the graph base coordinate maps to `p`. -/
def polynomialGraphEquiv (p : R[X]) : polynomialGraphRing p ≃+* R[X] :=
  RingEquiv.ofRingHom (polynomialGraphToPolynomial p) (polynomialToGraph p)
    (polynomialGraph_right_inverse p) (polynomialGraph_left_inverse p)

theorem polynomialGraphEquiv_base_variable (p : R[X]) :
    polynomialGraphEquiv p
      (Ideal.Quotient.mk (Ideal.span {graphPolynomialRelation p}) (MvPolynomial.C X)) = p := by
  change graphEvaluation p (MvPolynomial.C X) = p
  simp [graphEvaluation]

/-- The graph lift intertwines the two formal derivatives. -/
theorem graphPolynomialLift_derivative (p : R[X]) :
    MvPolynomial.pderiv () (graphPolynomialLift p) = graphPolynomialLift p.derivative := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    rw [map_add, map_add, derivative_add, map_add, hp, hq]
  | monomial n r =>
    simp only [graphPolynomialLift, coe_eval₂RingHom, eval₂_monomial, RingHom.comp_apply,
      MvPolynomial.pderiv_C_mul, MvPolynomial.pderiv_pow, MvPolynomial.pderiv_X_self,
      mul_one, derivative_monomial]
    simp only [map_mul, map_natCast]
    ring

/-- Under graph elimination, the selected Jacobian is minus the original derivative. -/
theorem polynomialGraphEquiv_jacobian (p : R[X]) :
    polynomialGraphEquiv p
      (Ideal.Quotient.mk (Ideal.span {graphPolynomialRelation p})
        (MvPolynomial.pderiv () (graphPolynomialRelation p))) = -p.derivative := by
  change graphEvaluation p (MvPolynomial.pderiv () (graphPolynomialRelation p)) = _
  rw [graphPolynomialRelation, map_sub, MvPolynomial.pderiv_C, graphPolynomialLift_derivative,
    zero_sub, map_neg]
  exact congrArg Neg.neg (congrArg (fun f : R[X] →+* R[X] => f p.derivative) (graphEvaluation_lift p))

/-- The graph neighborhood where the coordinate derivative is invertible. -/
abbrev polynomialCoordinateChart (p : R[X]) :=
  HypersurfaceChart.Construction.hypersurfaceDerivativeChart (graphPolynomialRelation p) ()

/-- Its map from the original ambient coordinate ring. -/
def polynomialCoordinateAmbientMap (p : R[X]) : R[X] →+* polynomialCoordinateChart p :=
  (algebraMap (polynomialGraphRing p) (polynomialCoordinateChart p)).comp (polynomialToGraph p)

/-- The replacement coordinate gives an étale algebra on this neighborhood. -/
theorem polynomialCoordinateChart_etale (p : R[X]) : Algebra.Etale R[X] (polynomialCoordinateChart p) :=
  oneVariable_hypersurfaceDerivativeChart_etale (graphPolynomialRelation p)

/-- The same neighborhood is an actual open subscheme of the original affine line. -/
theorem polynomialCoordinateAmbientMap_isOpenImmersion (p : R[X]) :
    AlgebraicGeometry.IsOpenImmersion
      (AlgebraicGeometry.Spec.map (CommRingCat.ofHom (polynomialCoordinateAmbientMap p))) := by
  let f : CommRingCat.of R[X] ⟶ CommRingCat.of (polynomialGraphRing p) :=
    CommRingCat.ofHom (polynomialToGraph p)
  let g : CommRingCat.of (polynomialGraphRing p) ⟶ CommRingCat.of (polynomialCoordinateChart p) :=
    CommRingCat.ofHom (algebraMap (polynomialGraphRing p) (polynomialCoordinateChart p))
  let : CategoryTheory.IsIso f := (ConcreteCategory.isIso_iff_bijective f).mpr
    (polynomialGraphEquiv p).symm.bijective
  let : AlgebraicGeometry.IsOpenImmersion (AlgebraicGeometry.Spec.map g) :=
    AlgebraicGeometry.IsOpenImmersion.of_isLocalization
      (Ideal.Quotient.mk (Ideal.span {graphPolynomialRelation p})
        (MvPolynomial.pderiv () (graphPolynomialRelation p)))
  change AlgebraicGeometry.IsOpenImmersion (AlgebraicGeometry.Spec.map (f ≫ g))
  rw [AlgebraicGeometry.Spec.map_comp]
  infer_instance

/-- On this open chart, the new base coordinate is exactly the original polynomial. -/
theorem polynomialCoordinateChart_coordinate (p : R[X]) :
    polynomialCoordinateAmbientMap p p = algebraMap R[X] (polynomialCoordinateChart p) X := by
  rw [polynomialCoordinateAmbientMap, RingHom.comp_apply, polynomialGraph_relation]
  exact (IsScalarTower.algebraMap_apply R[X] (polynomialGraphRing p) (polynomialCoordinateChart p) X).symm

variable {K : Type*} [Field K]

/-- A point where the derivative is nonzero lifts to the coordinate chart. -/
def polynomialCoordinatePoint (p : K[X]) (x : K) (hx : p.derivative.eval x ≠ 0) :
    polynomialCoordinateChart p →+* K :=
  IsLocalization.Away.lift
    (g := (evalRingHom x).comp (polynomialGraphEquiv p).toRingHom)
    (Ideal.Quotient.mk (Ideal.span {graphPolynomialRelation p})
      (MvPolynomial.pderiv () (graphPolynomialRelation p))) (by
      change IsUnit ((polynomialGraphEquiv p
        (Ideal.Quotient.mk (Ideal.span {graphPolynomialRelation p})
          (MvPolynomial.pderiv () (graphPolynomialRelation p)))).eval x)
      rw [polynomialGraphEquiv_jacobian, eval_neg]
      exact isUnit_iff_ne_zero.mpr (neg_ne_zero.mpr hx))

theorem polynomialCoordinatePoint_ambient (p : K[X]) (x : K) (hx : p.derivative.eval x ≠ 0)
    (r : K[X]) :
    polynomialCoordinatePoint p x hx (polynomialCoordinateAmbientMap p r) = r.eval x := by
  unfold polynomialCoordinatePoint polynomialCoordinateAmbientMap
  rw [RingHom.comp_apply, IsLocalization.Away.lift_eq]
  change ((polynomialGraphEquiv p) (polynomialToGraph p r)).eval x = r.eval x
  exact congrArg (fun q : K[X] => q.eval x) ((polynomialGraphEquiv p).apply_symm_apply r)

end

/-! Étale polynomial coordinates near a point with a nonzero partial derivative. -/

open _root_.Polynomial _root_.CategoryTheory _root_.AlgebraicGeometry

variable {R K : Type*} [CommRing R] [Field K]

/-- The graph coordinate neighborhood also admits points with a prescribed
coefficient map into a field. -/
def polynomialCoordinatePointOver (p : R[X]) (φ : R →+* K) (x : K)
    (hx : p.derivative.eval₂ φ x ≠ 0) : polynomialCoordinateChart p →+* K :=
  IsLocalization.Away.lift
    (g := (eval₂RingHom φ x).comp (polynomialGraphEquiv p).toRingHom)
    (Ideal.Quotient.mk (Ideal.span {graphPolynomialRelation p})
      (MvPolynomial.pderiv () (graphPolynomialRelation p))) (by
      change IsUnit ((polynomialGraphEquiv p
        (Ideal.Quotient.mk (Ideal.span {graphPolynomialRelation p})
          (MvPolynomial.pderiv () (graphPolynomialRelation p)))).eval₂ φ x)
      rw [polynomialGraphEquiv_jacobian, eval₂_neg]
      exact isUnit_iff_ne_zero.mpr (neg_ne_zero.mpr hx))

theorem polynomialCoordinatePointOver_ambient (p : R[X]) (φ : R →+* K) (x : K)
    (hx : p.derivative.eval₂ φ x ≠ 0) (r : R[X]) :
    polynomialCoordinatePointOver p φ x hx (polynomialCoordinateAmbientMap p r) = r.eval₂ φ x := by
  unfold polynomialCoordinatePointOver polynomialCoordinateAmbientMap
  rw [RingHom.comp_apply, IsLocalization.Away.lift_eq]
  change ((polynomialGraphEquiv p) (polynomialToGraph p r)).eval₂ φ x = r.eval₂ φ x
  exact congrArg (fun q : R[X] => q.eval₂ φ x) ((polynomialGraphEquiv p).apply_symm_apply r)

theorem polynomialCoordinateAmbientMap_C (p : R[X]) (r : R) :
    polynomialCoordinateAmbientMap p (C r) = algebraMap R[X] (polynomialCoordinateChart p) (C r) := by
  have h : polynomialToGraph p (C r) =
      Ideal.Quotient.mk (Ideal.span {graphPolynomialRelation p}) (MvPolynomial.C (C r)) := by
    simp [polynomialToGraph, graphPolynomialLift]
  rw [polynomialCoordinateAmbientMap, RingHom.comp_apply, h]
  exact (IsScalarTower.algebraMap_apply R[X] (polynomialGraphRing p) (polynomialCoordinateChart p) (C r)).symm

variable {σ : Type*}

/-- Separating the distinguished variable intertwines its partial derivative
with the ordinary polynomial derivative. -/
theorem optionEquivLeft_derivative (q : MvPolynomial (Option σ) R) :
    (MvPolynomial.optionEquivLeft R σ q).derivative =
      MvPolynomial.optionEquivLeft R σ (MvPolynomial.pderiv none q) := by
  classical
  induction q using MvPolynomial.induction_on with
  | C r => simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p i hp =>
    cases i <;> simp [Polynomial.derivative_mul, hp] <;> ring

/-- Evaluation is unchanged when a polynomial is written using a separated variable. -/
theorem optionEquivLeft_eval₂ (q : MvPolynomial (Option σ) R) (a : Option σ → R) :
    (MvPolynomial.optionEquivLeft R σ q).eval₂ (MvPolynomial.eval (fun s => a (some s))) (a none) =
      MvPolynomial.eval a q := by
  have ha : (fun o => Option.elim o (a none) (fun s => a (some s))) = a := by
    funext o
    cases o <;> rfl
  rw [eval₂_eq_eval_map]
  simpa only [ha] using
    (MvPolynomial.optionEquivLeft_elim_eval R σ (fun s => a (some s)) (a none) q).symm

/-- The graph neighborhood for a multivariate polynomial and its distinguished variable. -/
abbrev localPolynomialCoordinateChart (q : MvPolynomial (Option σ) K) :=
  polynomialCoordinateChart (MvPolynomial.optionEquivLeft K σ q)

def localPolynomialAmbientMap (q : MvPolynomial (Option σ) K) :
    MvPolynomial (Option σ) K →+* localPolynomialCoordinateChart q :=
  (polynomialCoordinateAmbientMap (MvPolynomial.optionEquivLeft K σ q)).comp
    (MvPolynomial.optionEquivLeft K σ).toRingHom

def localPolynomialCoordinateMap (q : MvPolynomial (Option σ) K) :
    MvPolynomial (Option σ) K →+* localPolynomialCoordinateChart q :=
  (algebraMap (MvPolynomial σ K)[X] (localPolynomialCoordinateChart q)).comp
    (MvPolynomial.optionEquivLeft K σ).toRingHom

/-- The new distinguished coordinate is precisely `q`. -/
theorem localPolynomialCoordinateMap_none (q : MvPolynomial (Option σ) K) :
    localPolynomialCoordinateMap q (MvPolynomial.X none) = localPolynomialAmbientMap q q := by
  change algebraMap (MvPolynomial σ K)[X] (localPolynomialCoordinateChart q)
      (MvPolynomial.optionEquivLeft K σ (MvPolynomial.X none)) =
    polynomialCoordinateAmbientMap (MvPolynomial.optionEquivLeft K σ q)
      (MvPolynomial.optionEquivLeft K σ q)
  rw [MvPolynomial.optionEquivLeft_X_none]
  exact (polynomialCoordinateChart_coordinate (MvPolynomial.optionEquivLeft K σ q)).symm

/-- All the other coordinates are retained. -/
theorem localPolynomialCoordinateMap_some (q : MvPolynomial (Option σ) K) (s : σ) :
    localPolynomialCoordinateMap q (MvPolynomial.X (some s)) =
      localPolynomialAmbientMap q (MvPolynomial.X (some s)) := by
  change algebraMap (MvPolynomial σ K)[X] (localPolynomialCoordinateChart q)
      (MvPolynomial.optionEquivLeft K σ (MvPolynomial.X (some s))) =
    polynomialCoordinateAmbientMap (MvPolynomial.optionEquivLeft K σ q)
      (MvPolynomial.optionEquivLeft K σ (MvPolynomial.X (some s)))
  rw [MvPolynomial.optionEquivLeft_X_some]
  exact (polynomialCoordinateAmbientMap_C _ _).symm

/-- Every point with a nonzero distinguished partial derivative lifts to
this coordinate neighborhood with all its original polynomial coordinates. -/
theorem localPolynomialCoordinateChart_has_point
    (q : MvPolynomial (Option σ) K) (a : Option σ → K)
    (ha : MvPolynomial.eval a (MvPolynomial.pderiv none q) ≠ 0) :
    ∃ e : localPolynomialCoordinateChart q →+* K,
      ∀ r : MvPolynomial (Option σ) K, e (localPolynomialAmbientMap q r) = MvPolynomial.eval a r := by
  have hd : (MvPolynomial.optionEquivLeft K σ q).derivative.eval₂
      (MvPolynomial.eval (fun s => a (some s))) (a none) ≠ 0 := by
    rw [optionEquivLeft_derivative, optionEquivLeft_eval₂]
    exact ha
  refine ⟨polynomialCoordinatePointOver _ _ _ hd, ?_⟩
  intro r
  rw [localPolynomialAmbientMap, RingHom.comp_apply, polynomialCoordinatePointOver_ambient]
  exact optionEquivLeft_eval₂ r a

/-- The coordinate neighborhood is an open subscheme of the original multivariate affine space. -/
theorem localPolynomialAmbientMap_isOpenImmersion (q : MvPolynomial (Option σ) K) :
    IsOpenImmersion (Spec.map (CommRingCat.ofHom (localPolynomialAmbientMap q))) := by
  let e := (MvPolynomial.optionEquivLeft K σ).toRingEquiv.toCommRingCatIso
  let f : CommRingCat.of (MvPolynomial σ K)[X] ⟶ CommRingCat.of (localPolynomialCoordinateChart q) :=
    CommRingCat.ofHom (polynomialCoordinateAmbientMap (MvPolynomial.optionEquivLeft K σ q))
  let : IsOpenImmersion (Spec.map f) :=
    polynomialCoordinateAmbientMap_isOpenImmersion (MvPolynomial.optionEquivLeft K σ q)
  change IsOpenImmersion (Spec.map (e.hom ≫ f))
  rw [Spec.map_comp]
  infer_instance

/-- Replacing the distinguished coordinate by `q` is étale on this open neighborhood. -/
theorem localPolynomialCoordinateMap_etale (q : MvPolynomial (Option σ) K) :
    Etale (Spec.map (CommRingCat.ofHom (localPolynomialCoordinateMap q))) := by
  let e := (MvPolynomial.optionEquivLeft K σ).toRingEquiv.toCommRingCatIso
  let f : CommRingCat.of (MvPolynomial σ K)[X] ⟶ CommRingCat.of (localPolynomialCoordinateChart q) :=
    CommRingCat.ofHom (algebraMap (MvPolynomial σ K)[X] (localPolynomialCoordinateChart q))
  let : Etale (Spec.map f) := oneVariable_hypersurfaceDerivativeChart_scheme_etale
    (graphPolynomialRelation (MvPolynomial.optionEquivLeft K σ q))
  change Etale (Spec.map (e.hom ≫ f))
  rw [Spec.map_comp]
  infer_instance

end

end OAI.AlgebraicGeometry.Resolution.Blowups.PolynomialEtale.Construction
