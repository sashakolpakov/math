import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Presentations.EndomorphismBridge
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.CM.GeneratorCriterion

/-! # Generator -/

namespace OAI

noncomputable section

namespace AlgebraicGeometry.PELModuli.IntegralModel.Presentations.Generator.EndomorphismFamilies

/-! Concrete finite Presentations equations for one primitive generator: its integral
minimal polynomial, and the conductor-divisibility equations on the actual
finite étale torsion scheme. All comparison maps are natural on arbitrary
test schemes. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite _root_.Polynomial

variable {S : Scheme} {g : ℕ} (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S)

def polynomialEndomorphismMap (p : ℤ[X]) :
    (EndomorphismFamiliesId.EndomorphismFamilies.endomorphismFunctor A ⋙ forget RingCat) ⟶ (EndomorphismFamiliesId.EndomorphismFamilies.endomorphismFunctor A ⋙ forget RingCat) where
  app _ := ↾fun u => aeval u p
  naturality {T U} f := by
    apply ConcreteCategory.hom_ext
    intro u
    exact aeval_algHom_apply (EndomorphismFamiliesId.EndomorphismFamilies.restrict A f.unop).toIntAlgHom u p

def e34PrimitivePolynomialMap (p : ℤ[X]) :
    HilbertScheme.Presentations.Endomorphisms.Core.endomorphismTuples A.scheme 1 ⟶ HilbertScheme.Presentations.HomFunctor.Hom.morphismFunctor A.scheme A.scheme :=
  EndomorphismBridge.EndomorphismFamilies.e34PrimitiveEndomorphism A ≫ polynomialEndomorphismMap A p ≫ EndomorphismHom.EndomorphismFamilies.homInclusion A

def homPrecomposition {X Y Z : Over S} (i : X ⟶ Y) :
    HilbertScheme.Presentations.HomFunctor.Hom.morphismFunctor Y Z ⟶ HilbertScheme.Presentations.HomFunctor.Hom.morphismFunctor X Z where
  app T := ↾fun f => prod.map (𝟙 T.unop) i ≫ f
  naturality {T U} a := by
    apply ConcreteCategory.hom_ext
    intro f
    change T.unop ⨯ Y ⟶ Z at f
    change prod.map (𝟙 U.unop) i ≫ (prod.map a.unop (𝟙 Y) ≫ f) =
      prod.map a.unop (𝟙 X) ≫ (prod.map (𝟙 T.unop) i ≫ f)
    simp only [← Category.assoc, prod.map_map, Category.id_comp, Category.comp_id]

def e34PolynomialEquation (p : ℤ[X]) :
    HilbertScheme.Presentations.Endomorphisms.Core.FamilyMorphismEquation (HilbertScheme.Presentations.Endomorphisms.Core.endomorphismTuples A.scheme 1) where
  source := A.scheme
  target := A.scheme
  flat := inferInstance
  proper := inferInstance
  finitelyPresented := inferInstance
  separated := inferInstance
  lhs := e34PrimitivePolynomialMap A p
  rhs := e34PrimitivePolynomialMap A 0

def e34TorsionPolynomialEquation (c : ℕ)
    (hc : ∀ s : S, IsUnit (c : S.presheaf.stalk s)) (p : ℤ[X]) :
    HilbertScheme.Presentations.Endomorphisms.Core.FamilyMorphismEquation (HilbertScheme.Presentations.Endomorphisms.Core.endomorphismTuples A.scheme 1) where
  source := A.torsionScheme c
  target := A.scheme
  flat := by
    have := (TorsionDivision.torsionScheme_finite_etale A c hc).2
    infer_instance
  proper := inferInstance
  finitelyPresented := by
    have := (TorsionDivision.torsionScheme_finite_etale A c hc).2
    infer_instance
  separated := inferInstance
  lhs := e34PrimitivePolynomialMap A p ≫ homPrecomposition (A.torsionInclusion c)
  rhs := e34PrimitivePolynomialMap A 0 ≫ homPrecomposition (A.torsionInclusion c)

variable {E : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]
  (D : CM.GeneratorReconstruction.CMIntegralGeneratorData E)

def e34IntegralGeneratorEquations
    (hc : ∀ s : S, IsUnit (D.conductor : S.presheaf.stalk s)) :
    HilbertScheme.Presentations.Endomorphisms.Core.FiniteEndomorphismEquations A.scheme 1 :=
  e34PolynomialEquation A (minpoly ℤ (D.generator : E)) ::
    (List.ofFn (fun i : Fin (Module.finrank ℤ (NumberField.RingOfIntegers E)) =>
      e34TorsionPolynomialEquation A D.conductor hc (D.polynomial (Finite.Actions.integralActionBasis E i))))

end AlgebraicGeometry.PELModuli.IntegralModel.Presentations.Generator.EndomorphismFamilies

namespace AlgebraicGeometry.PELModuli.IntegralModel.Presentations.Generator
section

/-! Compare restriction to the actual torsion scheme with the parameterized
restriction used in Presentations, on every test scheme. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite _root_.Polynomial
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

variable {S : Scheme} {g : ℕ} (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S)

theorem torsion_restriction_zero_iff (c : ℕ) (p : A.scheme ⟶ A.scheme) :
    A.torsionInclusion c ≫ p = 1 ↔
      ∀ (Q : Over S) (x : Q ⟶ A.scheme), x ^ c = 1 → x ≫ p = 1 := by
  constructor
  · intro hp Q x hx
    let t := (A.torsionSchemePointsEquiv c Q).symm ⟨x, hx⟩
    have ht : t ≫ A.torsionInclusion c = x :=
      congrArg Subtype.val ((A.torsionSchemePointsEquiv c Q).apply_symm_apply ⟨x, hx⟩)
    rw [← ht, Category.assoc, hp, MonObj.comp_one]
  · intro h
    exact h (A.torsionScheme c) (A.torsionInclusion c) (A.torsionInclusion_pow c)

namespace EndomorphismFamilies

theorem relativeHomEquiv_one (T : Over S) :
    EndomorphismHom.EndomorphismFamilies.relativeHomEquiv A T (1 : (A.pullback T.hom).scheme ⟶ (A.pullback T.hom).scheme) = 1 := by
  let W := T ⨯ A.scheme
  let b : W ⟶ T := prod.fst
  let e := IntrinsicGroupHomEquations.GroupHomEquations.parameterPointsMulEquiv A.scheme T W b
  have h := IntrinsicGroupHomEquations.GroupHomEquations.native_parameter_evaluation A.scheme T
    (1 : (A.pullback T.hom).scheme ⟶ (A.pullback T.hom).scheme) W b
    (e.symm (prod.snd : W ⟶ A.scheme))
  change e (e.symm prod.snd ≫ (1 : (Over.pullback T.hom).obj A.scheme ⟶
    (Over.pullback T.hom).obj A.scheme)) =
      prod.lift b (e (e.symm prod.snd)) ≫ EndomorphismHom.EndomorphismFamilies.relativeHomEquiv A T 1 at h
  rw [MonObj.comp_one] at h
  rw [e.map_one, e.apply_symm_apply] at h
  change 1 = prod.lift (prod.fst : T ⨯ A.scheme ⟶ T) prod.snd ≫
    EndomorphismHom.EndomorphismFamilies.relativeHomEquiv A T 1 at h
  rw [prod.lift_fst_snd, Category.id_comp] at h
  exact h.symm

theorem relative_torsion_restriction_zero_iff (T : Over S) (c : ℕ)
    (r : (A.pullback T.hom).scheme ⟶ (A.pullback T.hom).scheme) :
    (A.pullback T.hom).torsionInclusion c ≫ r = 1 ↔
      prod.map (𝟙 T) (A.torsionInclusion c) ≫ EndomorphismHom.EndomorphismFamilies.relativeHomEquiv A T r = 1 := by
  change (Over.pullback T.hom).obj A.scheme ⟶ (Over.pullback T.hom).obj A.scheme at r
  constructor
  · intro hr
    let W := T ⨯ A.torsionScheme c
    let b : W ⟶ T := prod.fst
    let y : W ⟶ A.scheme := prod.snd ≫ A.torsionInclusion c
    have hy : y ^ c = 1 := by
      rw [show y = prod.snd ≫ A.torsionInclusion c from rfl,
        ← MonObj.comp_pow, A.torsionInclusion_pow, MonObj.comp_one]
    let e := IntrinsicGroupHomEquations.GroupHomEquations.parameterPointsMulEquiv A.scheme T W b
    have hx : (e.symm y) ^ c = 1 := by
      rw [← map_pow e.symm, hy, e.symm.map_one]
    have hzero := (torsion_restriction_zero_iff (A.pullback T.hom) c r).mp hr
      (Over.mk b.left) (e.symm y) hx
    change e.symm y ≫ r = (1 : Over.mk b.left ⟶ (Over.pullback T.hom).obj A.scheme) at hzero
    have h := IntrinsicGroupHomEquations.GroupHomEquations.native_parameter_evaluation A.scheme T r W b (e.symm y)
    change e (e.symm y ≫ r) = prod.lift b (e (e.symm y)) ≫ EndomorphismHom.EndomorphismFamilies.relativeHomEquiv A T r at h
    rw [hzero, e.map_one, e.apply_symm_apply] at h
    have hmap : prod.lift b y = prod.map (𝟙 T) (A.torsionInclusion c) := by
      dsimp [b, y, W]
      apply prod.hom_ext
      · rw [prod.map_fst, Category.comp_id]
        exact prod.lift_fst _ _
      · rw [prod.map_snd]
        exact prod.lift_snd _ _
    rw [hmap] at h
    exact h.symm
  · intro hr
    apply (torsion_restriction_zero_iff (A.pullback T.hom) c r).mpr
    intro Q x hx
    change Q ⟶ (Over.pullback T.hom).obj A.scheme at x
    change x ^ c = (1 : Q ⟶ (Over.pullback T.hom).obj A.scheme) at hx
    let e := Group.PointsBaseChange.GroupPoints.baseChangePointsMulEquiv A.scheme T.hom Q
    have hy : (e x) ^ c = 1 := by rw [← map_pow e, hx, e.map_one]
    let t := (A.torsionSchemePointsEquiv c ((Over.map T.hom).obj Q)).symm ⟨e x, hy⟩
    have ht : t ≫ A.torsionInclusion c = e x :=
      congrArg Subtype.val
        ((A.torsionSchemePointsEquiv c ((Over.map T.hom).obj Q)).apply_symm_apply ⟨e x, hy⟩)
    apply e.injective
    change Group.PointsBaseChange.GroupPoints.baseChangePointsMulEquiv A.scheme T.hom Q (x ≫ r) = e 1
    rw [IntrinsicGroupHomPoints.GroupHomEquations.native_evaluation, e.map_one]
    change prod.lift (IntrinsicGroupHomPoints.GroupHomEquations.parameterProjection T Q) (e x) ≫
      EndomorphismHom.EndomorphismFamilies.relativeHomEquiv A T r = 1
    have hpair : prod.lift (IntrinsicGroupHomPoints.GroupHomEquations.parameterProjection T Q) (e x) =
        prod.lift (IntrinsicGroupHomPoints.GroupHomEquations.parameterProjection T Q) t ≫
          prod.map (𝟙 T) (A.torsionInclusion c) := by
      apply prod.hom_ext <;> simp [ht]
    rw [hpair, Category.assoc, hr, MonObj.comp_one]

end EndomorphismFamilies

end

/-! The concrete Presentations equations are exactly the finite criterion that
constructs an integral CM action, on arbitrary test schemes. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite _root_.Polynomial
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

namespace EndomorphismFamilies

variable {S : Scheme} {g : ℕ} (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S)

def e34GeneratorTuple (T : Over S) (u : Finite.Actions.GroupEndRing (A.pullback T.hom)) :
    (HilbertScheme.Presentations.Endomorphisms.Core.endomorphismTuples A.scheme 1).obj (op T) :=
  fun _ => EndomorphismBridge.EndomorphismFamilies.e34EndomorphismEquiv A T u

@[simp] theorem e34Primitive_generatorTuple (T : Over S) (u : Finite.Actions.GroupEndRing (A.pullback T.hom)) :
    (EndomorphismBridge.EndomorphismFamilies.e34PrimitiveEndomorphism A).app (op T) (e34GeneratorTuple A T u) = u :=
  (EndomorphismBridge.EndomorphismFamilies.e34EndomorphismEquiv A T).symm_apply_apply u

theorem e34Primitive_injective (T : Over S) :
    Function.Injective ((EndomorphismBridge.EndomorphismFamilies.e34PrimitiveEndomorphism A).app (op T)) := by
  intro f h heq
  change (EndomorphismBridge.EndomorphismFamilies.e34EndomorphismEquiv A T).symm (f 0) =
    (EndomorphismBridge.EndomorphismFamilies.e34EndomorphismEquiv A T).symm (h 0) at heq
  have hzero := (EndomorphismBridge.EndomorphismFamilies.e34EndomorphismEquiv A T).symm.injective heq
  funext i
  have hi : i = 0 := Subsingleton.elim _ _
  exact hi ▸ hzero

theorem e34PolynomialEquation_iff (T : Over S)
    (f : (HilbertScheme.Presentations.Endomorphisms.Core.endomorphismTuples A.scheme 1).obj (op T)) (p : ℤ[X]) :
    (e34PolynomialEquation A p).lhs.app (op T) f =
        (e34PolynomialEquation A p).rhs.app (op T) f ↔
      aeval ((EndomorphismBridge.EndomorphismFamilies.e34PrimitiveEndomorphism A).app (op T) f) p = 0 := by
  let u : Finite.Actions.GroupEndRing (A.pullback T.hom) := (EndomorphismBridge.EndomorphismFamilies.e34PrimitiveEndomorphism A).app (op T) f
  change (EndomorphismHom.EndomorphismFamilies.homInclusion A).app (op T) (aeval u p) =
    (EndomorphismHom.EndomorphismFamilies.homInclusion A).app (op T) (aeval u 0) ↔ aeval u p = 0
  rw [map_zero]
  exact (EndomorphismHom.EndomorphismFamilies.homInclusion_injective A T).eq_iff

theorem e34TorsionPolynomialEquation_iff (T : Over S)
    (f : (HilbertScheme.Presentations.Endomorphisms.Core.endomorphismTuples A.scheme 1).obj (op T)) (c : ℕ)
    (hc : ∀ s : S, IsUnit (c : S.presheaf.stalk s)) (p : ℤ[X]) :
    (e34TorsionPolynomialEquation A c hc p).lhs.app (op T) f =
        (e34TorsionPolynomialEquation A c hc p).rhs.app (op T) f ↔
      (A.pullback T.hom).torsionInclusion c ≫
        (aeval ((EndomorphismBridge.EndomorphismFamilies.e34PrimitiveEndomorphism A).app (op T) f) p).hom (A.pullback T.hom) = 1 := by
  let u : Finite.Actions.GroupEndRing (A.pullback T.hom) := (EndomorphismBridge.EndomorphismFamilies.e34PrimitiveEndomorphism A).app (op T) f
  change prod.map (𝟙 T) (A.torsionInclusion c) ≫
      EndomorphismHom.EndomorphismFamilies.relativeHomEquiv A T ((aeval u p).hom (A.pullback T.hom)) =
    prod.map (𝟙 T) (A.torsionInclusion c) ≫
      EndomorphismHom.EndomorphismFamilies.relativeHomEquiv A T ((aeval u 0).hom (A.pullback T.hom)) ↔ _
  rw [map_zero, Finite.Actions.GroupEndRing.hom_zero, relativeHomEquiv_one, MonObj.comp_one]
  exact (relative_torsion_restriction_zero_iff A T c _).symm

variable {E : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]
  (D : CM.GeneratorReconstruction.CMIntegralGeneratorData E)

theorem e34IntegralGeneratorEquations_iff
    (hc : ∀ s : S, IsUnit (D.conductor : S.presheaf.stalk s)) (T : Over S)
    (f : (HilbertScheme.Presentations.Endomorphisms.Core.endomorphismTuples A.scheme 1).obj (op T)) :
    HilbertScheme.Presentations.Endomorphisms.Core.SatisfiesEquations (e34IntegralGeneratorEquations A D hc) f ↔
      D.GeneratorConditions (A.pullback T.hom) ((EndomorphismBridge.EndomorphismFamilies.e34PrimitiveEndomorphism A).app (op T) f) := by
  constructor
  · intro h
    constructor
    · apply (e34PolynomialEquation_iff A T f _).mp
      exact h _ List.mem_cons_self
    · intro i
      apply (e34TorsionPolynomialEquation_iff A T f _ hc _).mp
      exact h _ (List.mem_cons_of_mem _ (List.mem_ofFn.mpr ⟨i, rfl⟩))
  · intro h r hr
    rcases List.mem_cons.mp hr with hr | hr
    · subst r
      exact (e34PolynomialEquation_iff A T f _).mpr h.1
    · obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hr
      exact (e34TorsionPolynomialEquation_iff A T f _ hc _).mpr (h.2 i)

end EndomorphismFamilies

end AlgebraicGeometry.PELModuli.IntegralModel.Presentations.Generator

end

end OAI
