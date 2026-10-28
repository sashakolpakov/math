import OAI.AlgebraicGeometry.PELModuli.IntegralModel.CountableParameters
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Base

/-! # Parameters -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.Arithmetic.Parameters

noncomputable section

/-! Arithmetic descent of an isolated parameter over a specified number
field and complex embedding. The finite field extension, its extending
complex embedding, and the actual descended parameter point are constructed. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

variable {K : Type} [Field K] [NumberField K] (κ : K →+* ℂ)
  (X : Over (Spec (.of K))) [LocallyOfFiniteType X.hom]

/-- A closed parameter point produces the exact finite extension and
embedding data needed by ArithmeticBaseExtension. -/
theorem parameter_finite_extension_of_closed
    (p : Spec (.of ℂ) ⟶ X.left) (hp : p ≫ X.hom = Spec.map (CommRingCat.ofHom κ))
    (hclosed : IsClosed {p (IsLocalRing.closedPoint ℂ)}) (N : ℕ) (hN : N ≠ 0) :
    ∃ (B : Base.ArithmeticBaseExtension K κ) (pL : Spec (.of B.extension.carrier) ⟶ X.left),
      B.denominator = N ∧ pL ≫ X.hom = B.fieldExtension ∧
        Spec.map (CommRingCat.ofHom B.embedding) ≫ pL = p := by
  let qK := Spec.map (CommRingCat.ofHom (algebraMap ℚ K))
  have : IsFinite qK := by
    apply (IsFinite.SpecMap_iff _).mpr
    exact RingHom.finite_algebraMap.mpr inferInstance
  have : LocallyOfFiniteType (X.hom ≫ qK) := inferInstance
  obtain ⟨L, hL, pL, hfactor⟩ := ArithmeticGeometry.Descent.CMVariety.AlgebraicPoints.Abelian.complex_point_descends_of_closed (X.hom ≫ qK) p hclosed
  let := hL
  let j : K →+* L := (Spec.preimage (pL ≫ X.hom)).hom
  have hj : Spec.map (CommRingCat.ofHom j) = pL ≫ X.hom := Spec.map_preimage _
  have he : L.subtype.comp j = κ := by
    have hs : Spec.map (CommRingCat.ofHom (L.subtype.comp j)) =
        Spec.map (CommRingCat.ofHom κ) := by
      change Spec.map (CommRingCat.ofHom j ≫ CommRingCat.ofHom L.subtype) = _
      rw [Spec.map_comp, hj, ← Category.assoc, hfactor, hp]
    exact congrArg CommRingCat.Hom.hom (Spec.map_injective hs)
  let : Algebra K L := j.toAlgebra
  have : FiniteDimensional K L := Module.Finite.of_restrictScalars_finite ℚ K L
  let B : Base.ArithmeticBaseExtension K κ := {
    extension := ⟨L⟩
    embedding := L.subtype
    embedding_extends := he
    denominator := N
    denominator_ne_zero := hN }
  exact ⟨B, pL, rfl, hj.symm, hfactor⟩

/-- Isolation on the selected complex fiber suffices, with the prescribed
embedding retained throughout the actual parameter factorization. -/
theorem parameter_finite_extension_of_isolated_fiber
    (p : CountableParameters.ParameterPoints ((Over.pullback (Spec.map (CommRingCat.ofHom κ))).obj X))
    (hopen : IsOpen {p.left (IsLocalRing.closedPoint ℂ)}) (N : ℕ) (hN : N ≠ 0) :
    ∃ (B : Base.ArithmeticBaseExtension K κ) (pL : Spec (.of B.extension.carrier) ⟶ X.left),
      B.denominator = N ∧ pL ≫ X.hom = B.fieldExtension ∧
        Spec.map (CommRingCat.ofHom B.embedding) ≫ pL =
          p.left ≫ pullback.fst X.hom (Spec.map (CommRingCat.ofHom κ)) := by
  let π := pullback.fst X.hom (Spec.map (CommRingCat.ofHom κ))
  have hp : (p.left ≫ π) ≫ X.hom = Spec.map (CommRingCat.ofHom κ) := by
    rw [Category.assoc, pullback.condition, ← Category.assoc]
    have hw : p.left ≫ pullback.snd X.hom (Spec.map (CommRingCat.ofHom κ)) = 𝟙 _ := p.w
    rw [hw, Category.id_comp]
  have hpointOpen : IsOpen {(p.left ≫ π) (IsLocalRing.closedPoint ℂ)} := by
    change IsOpen {π (p.left (IsLocalRing.closedPoint ℂ))}
    simpa only [Set.image_singleton] using π.isOpenMap {p.left (IsLocalRing.closedPoint ℂ)} hopen
  have : JacobsonSpace X.left := LocallyOfFiniteType.jacobsonSpace X.hom
  exact parameter_finite_extension_of_closed κ X (p.left ≫ π) hp
    (isClosed_singleton_of_isLocallyClosed_singleton hpointOpen.isLocallyClosed) N hN

/-- A parameter functor with at most countably many points on the chosen
complex fiber has actual finite-extension models for each of its points. -/
theorem parameter_finite_extension_of_countable_fiber
    [Countable (CountableParameters.ParameterPoints ((Over.pullback (Spec.map (CommRingCat.ofHom κ))).obj X))]
    (p : CountableParameters.ParameterPoints ((Over.pullback (Spec.map (CommRingCat.ofHom κ))).obj X))
    (N : ℕ) (hN : N ≠ 0) :
    ∃ (B : Base.ArithmeticBaseExtension K κ) (pL : Spec (.of B.extension.carrier) ⟶ X.left),
      B.denominator = N ∧ pL ≫ X.hom = B.fieldExtension ∧
        Spec.map (CommRingCat.ofHom B.embedding) ≫ pL =
          p.left ≫ pullback.fst X.hom (Spec.map (CommRingCat.ofHom κ)) := by
  let XC := (Over.pullback (Spec.map (CommRingCat.ofHom κ))).obj X
  have : Uncountable ℂ := Complex.ofReal_injective.uncountable
  have : LocallyOfFiniteType XC.hom := inferInstanceAs
    (LocallyOfFiniteType (pullback.snd X.hom (Spec.map (CommRingCat.ofHom κ))))
  have : DiscreteTopology XC.left := CountableParameters.discrete_of_countable_parameter_points XC
  exact parameter_finite_extension_of_isolated_fiber κ X p (isOpen_discrete _) N hN

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.Arithmetic.Parameters
