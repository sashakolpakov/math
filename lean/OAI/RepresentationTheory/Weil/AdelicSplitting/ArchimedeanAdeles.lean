import OAI.RepresentationTheory.Weil.AdelicSplitting.QuadraticTopology
import OAI.RepresentationTheory.Weil.AdelicSplitting.RestrictedLimits

/-! # Archimedean Adeles -/

namespace OAI.RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction

noncomputable section

section

/-! Actual places, completions, adeles, and localization maps of a number field. -/

open scoped _root_.NumberField Classical
open IsDedekindDomain

variable (F : Type*) [Field F] [NumberField F]

abbrev Places := NumberField.InfinitePlace F ⊕ HeightOneSpectrum (𝓞 F)
abbrev Adeles := NumberField.AdeleRing (𝓞 F) F
abbrev FiniteAdeles := IsDedekindDomain.FiniteAdeleRing (𝓞 F) F

abbrev Completion : Places F → Type _
  | Sum.inl v => v.Completion
  | Sum.inr v => v.adicCompletion F

instance completionNormedField (v : Places F) : NormedField (Construction.Completion F v) :=
  match v with
  | Sum.inl _ => inferInstance
  | Sum.inr _ => inferInstance

instance completionCompleteSpace (v : Places F) : CompleteSpace (Construction.Completion F v) :=
  match v with
  | Sum.inl _ => inferInstance
  | Sum.inr _ => inferInstance

instance completionMeasurableSpace (v : Places F) : MeasurableSpace (Construction.Completion F v) :=
  borel (Construction.Completion F v)

instance completionBorelSpace (v : Places F) : BorelSpace (Construction.Completion F v) := ⟨rfl⟩

def evaluate (v : Places F) : Adeles F →+* Construction.Completion F v :=
  match v with
  | Sum.inl w =>
    { toFun := fun a => a.1 w
      map_zero' := rfl
      map_one' := rfl
      map_add' := fun _ _ => rfl
      map_mul' := fun _ _ => rfl }
  | Sum.inr w =>
    { toFun := fun a => a.2 w
      map_zero' := rfl
      map_one' := rfl
      map_add' := fun _ _ => rfl
      map_mul' := fun _ _ => rfl }

theorem evaluate_continuous (v : Places F) : Continuous (evaluate F v) := by
  cases v with
  | inl w => exact (continuous_apply w).comp continuous_fst
  | inr w => exact (RestrictedProduct.continuous_eval w).comp continuous_snd

def rationalScalar (v : Places F) : F →+* Construction.Completion F v :=
  (evaluate F v).comp (algebraMap F (Adeles F))

instance completionCharZero (v : Places F) : CharZero (Construction.Completion F v) :=
  charZero_of_injective_ringHom (rationalScalar F v).injective

theorem rationalScalar_injective (v : Places F) : Function.Injective (rationalScalar F v) :=
  (rationalScalar F v).injective

theorem adeles_ext {a b : Adeles F} (h : ∀ v, evaluate F v a = evaluate F v b) : a = b := by
  apply Prod.ext
  · funext v
    exact h (Sum.inl v)
  · apply IsDedekindDomain.FiniteAdeleRing.ext
    intro v
    exact h (Sum.inr v)

def localAdd (v : Places F) : Construction.Completion F v →+ Adeles F :=
  match v with
  | Sum.inl w =>
    { toFun := fun x => (Pi.single w x, 0)
      map_zero' := by
        change (Pi.single w (0 : w.Completion), (0 : FiniteAdeles F)) = (0, 0)
        rw [Pi.single_zero]
      map_add' := by
        intro x y
        change (Pi.single w (x + y), (0 : FiniteAdeles F)) =
          (Pi.single w x + Pi.single w y, 0 + 0)
        rw [Pi.single_add, add_zero] }
  | Sum.inr w =>
    { toFun := fun x => (0, RestrictedProduct.single
          (fun p : HeightOneSpectrum (𝓞 F) => p.adicCompletionIntegers F) w x)
      map_zero' := by
        change ((0 : NumberField.InfiniteAdeleRing F), RestrictedProduct.single
          (fun p : HeightOneSpectrum (𝓞 F) => p.adicCompletionIntegers F) w 0) = (0, 0)
        rw [RestrictedProduct.single_zero]
      map_add' := by
        intro x y
        change ((0 : NumberField.InfiniteAdeleRing F), RestrictedProduct.single
          (fun p : HeightOneSpectrum (𝓞 F) => p.adicCompletionIntegers F) w (x + y)) =
          (0 + 0, RestrictedProduct.single
            (fun p : HeightOneSpectrum (𝓞 F) => p.adicCompletionIntegers F) w x +
            RestrictedProduct.single
            (fun p : HeightOneSpectrum (𝓞 F) => p.adicCompletionIntegers F) w y)
        rw [RestrictedProduct.single_add, add_zero] }

@[simp] theorem evaluate_localAdd_same (v : Places F) (x : Construction.Completion F v) :
    evaluate F v (localAdd F v x) = x := by
  cases v with
  | inl w => exact Pi.single_eq_same w x
  | inr w =>
    exact RestrictedProduct.single_eq_same
      (fun p : HeightOneSpectrum (𝓞 F) => p.adicCompletionIntegers F) w x

@[simp] theorem evaluate_localAdd_other {v w : Places F} (h : w ≠ v)
    (x : Construction.Completion F v) : evaluate F w (localAdd F v x) = 0 := by
  cases v with
  | inl v =>
    cases w with
    | inl w =>
      change Pi.single v x w = 0
      have h' : w ≠ v := by simpa using h
      simp [Pi.single_eq_of_ne h']
    | inr w => rfl
  | inr v =>
    cases w with
    | inl w => rfl
    | inr w =>
      change RestrictedProduct.single
        (fun p : HeightOneSpectrum (𝓞 F) => p.adicCompletionIntegers F) v x w = 0
      exact RestrictedProduct.single_eq_of_ne
        (fun p : HeightOneSpectrum (𝓞 F) => p.adicCompletionIntegers F) x (by simpa using h)

abbrev localQuadratic (d : F) (v : Places F) := UnitaryBase.Construction.Quadratic (Construction.Completion F v) (rationalScalar F v d)
abbrev adelicQuadratic (d : F) := UnitaryBase.Construction.Quadratic (Adeles F) (algebraMap F (Adeles F) d)

def quadraticEvaluate (d : F) (v : Places F) :
    adelicQuadratic F d →+* localQuadratic F d v :=
  UnitaryBase.Construction.quadraticBaseChange (evaluate F v) (algebraMap F (Adeles F) d)

def quadraticRational : (d : F) → UnitaryBase.Construction.Quadratic F d →+* adelicQuadratic F d :=
  UnitaryBase.Construction.quadraticBaseChange (algebraMap F (Adeles F))

theorem quadraticEvaluate_continuous (d : F) (v : Places F) :
    Continuous (quadraticEvaluate F d v) :=
  QuadraticTopology.Construction.quadraticBaseChange_continuous (evaluate F v) (evaluate_continuous F v) _

end

/-! The actual archimedean adele ring identified topologically with the
usual real and complex Minkowski space. -/

open scoped Classical _root_.NumberField
open _root_.NumberField _root_.NumberField.InfinitePlace

variable (F : Type) [Field F]

def infiniteAdeleMixedHomeomorph :
    InfiniteAdeleRing F ≃ₜ mixedEmbedding.mixedSpace F :=
  (Homeomorph.piEquivPiSubtypeProd (fun v : InfinitePlace F => IsReal v)
    (fun v : InfinitePlace F => v.Completion)).trans
    ((Homeomorph.piCongrRight (fun v : {v : InfinitePlace F // IsReal v} =>
      (Completion.isometryEquivRealOfIsReal v.property).toHomeomorph)).prodCongr
      ((Homeomorph.piCongrRight (fun v : {v : InfinitePlace F // ¬ IsReal v} =>
        (Completion.isometryEquivComplexOfIsComplex
          (not_isReal_iff_isComplex.mp v.property)).toHomeomorph)).trans
        (Homeomorph.piCongrLeft (Y := fun _ : {v : InfinitePlace F // IsComplex v} => ℂ)
          (Equiv.subtypeEquivRight (fun _ => not_isReal_iff_isComplex)))))

theorem infiniteAdeleMixedHomeomorph_eq_ringEquiv (x : InfiniteAdeleRing F) :
    infiniteAdeleMixedHomeomorph F x = InfiniteAdeleRing.ringEquiv_mixedSpace F x := rfl

theorem infiniteAdeleMixedHomeomorph_rational (q : F) :
    infiniteAdeleMixedHomeomorph F (algebraMap F (InfiniteAdeleRing F) q) = mixedEmbedding F q :=
  (InfiniteAdeleRing.mixedEmbedding_eq_algebraMap_comp F (x := q)).symm

end

end OAI.RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction
