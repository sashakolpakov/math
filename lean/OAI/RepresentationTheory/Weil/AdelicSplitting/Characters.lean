import OAI.RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles

/-! # Characters -/

namespace OAI.RepresentationTheory.Weil.AdelicSplitting.Characters.Construction

noncomputable section

/-! Prescribed global characters and their actual local components.
The quadratic extension is presented as F[δ]/(δ²-d); scalar extension to
the adeles and to each completion automatically includes split places. -/

open scoped _root_.NumberField Classical

variable (F : Type*) [Field F] [NumberField F]

theorem localAdd_continuous (v : ArchimedeanAdeles.Construction.Places F) : Continuous (ArchimedeanAdeles.Construction.localAdd F v) := by
  cases v with
  | inl w => exact continuous_single w |>.prodMk continuous_const
  | inr w =>
    exact continuous_const.prodMk
      (RestrictedLimits.Construction.includeAddPlace_continuous
        (fun p : IsDedekindDomain.HeightOneSpectrum (𝓞 F) =>
          (p.adicCompletionIntegers F).toAddSubgroup) w)

def localAdditiveCharacter (ψ : AddChar (ArchimedeanAdeles.Construction.Adeles F) ℂ) (v : ArchimedeanAdeles.Construction.Places F) :
    AddChar (ArchimedeanAdeles.Construction.Completion F v) ℂ := ψ.compAddMonoidHom (ArchimedeanAdeles.Construction.localAdd F v)

theorem localAdditiveCharacter_continuous (ψ : AddChar (ArchimedeanAdeles.Construction.Adeles F) ℂ)
    (hψ : Continuous ψ) (v : ArchimedeanAdeles.Construction.Places F) : Continuous (localAdditiveCharacter F ψ v) :=
  hψ.comp (localAdd_continuous F v)

theorem localAdditiveCharacter_unitary (ψ : AddChar (ArchimedeanAdeles.Construction.Adeles F) ℂ)
    (hψ : ∀ x, ‖ψ x‖ = 1) (v : ArchimedeanAdeles.Construction.Places F) (x : ArchimedeanAdeles.Construction.Completion F v) :
    ‖localAdditiveCharacter F ψ v x‖ = 1 := hψ _

def quadraticLocalAdd (d : F) (v : ArchimedeanAdeles.Construction.Places F) :
    ArchimedeanAdeles.Construction.localQuadratic F d v →+ ArchimedeanAdeles.Construction.adelicQuadratic F d where
  toFun z := ⟨ArchimedeanAdeles.Construction.localAdd F v z.re, ArchimedeanAdeles.Construction.localAdd F v z.im⟩
  map_zero' := by ext <;> simp
  map_add' z w := by ext <;> simp [map_add]

theorem quadraticLocalAdd_continuous (d : F) (v : ArchimedeanAdeles.Construction.Places F) :
    Continuous (quadraticLocalAdd F d v) := by
  rw [QuadraticTopology.Construction.quadratic_continuous_iff]
  exact ⟨(localAdd_continuous F v).comp (QuadraticTopology.Construction.quadratic_continuous_re _),
    (localAdd_continuous F v).comp (QuadraticTopology.Construction.quadratic_continuous_im _)⟩

@[simp] theorem quadraticEvaluate_localAdd_same (d : F) (v : ArchimedeanAdeles.Construction.Places F)
    (z : ArchimedeanAdeles.Construction.localQuadratic F d v) :
    ArchimedeanAdeles.Construction.quadraticEvaluate F d v (quadraticLocalAdd F d v z) = z := by
  apply QuadraticAlgebra.ext
  · exact ArchimedeanAdeles.Construction.evaluate_localAdd_same F v z.re
  · exact ArchimedeanAdeles.Construction.evaluate_localAdd_same F v z.im

@[simp] theorem quadraticEvaluate_localAdd_other (d : F) {v w : ArchimedeanAdeles.Construction.Places F}
    (h : w ≠ v) (z : ArchimedeanAdeles.Construction.localQuadratic F d v) :
    ArchimedeanAdeles.Construction.quadraticEvaluate F d w (quadraticLocalAdd F d v z) = 0 := by
  apply QuadraticAlgebra.ext
  · exact ArchimedeanAdeles.Construction.evaluate_localAdd_other F h z.re
  · exact ArchimedeanAdeles.Construction.evaluate_localAdd_other F h z.im

theorem quadraticAdeles_ext (d : F) {a b : ArchimedeanAdeles.Construction.adelicQuadratic F d}
    (h : ∀ v, ArchimedeanAdeles.Construction.quadraticEvaluate F d v a = ArchimedeanAdeles.Construction.quadraticEvaluate F d v b) : a = b := by
  apply QuadraticAlgebra.ext
  · apply ArchimedeanAdeles.Construction.adeles_ext F
    intro v
    exact congrArg QuadraticAlgebra.re (h v)
  · apply ArchimedeanAdeles.Construction.adeles_ext F
    intro v
    exact congrArg QuadraticAlgebra.im (h v)

/-- A local idele has its given value at v and value one elsewhere. -/
def localIdeleElement (d : F) (v : ArchimedeanAdeles.Construction.Places F) (a : (ArchimedeanAdeles.Construction.localQuadratic F d v)ˣ) :
    (ArchimedeanAdeles.Construction.adelicQuadratic F d)ˣ where
  val := quadraticLocalAdd F d v (a.val - 1) + 1
  inv := quadraticLocalAdd F d v (a.inv - 1) + 1
  val_inv := by
    apply quadraticAdeles_ext F d
    intro w
    by_cases h : w = v
    · subst w
      simp only [map_mul, map_add, map_one, quadraticEvaluate_localAdd_same,
        sub_add_cancel, a.val_inv]
    · simp [quadraticEvaluate_localAdd_other F d h]
  inv_val := by
    apply quadraticAdeles_ext F d
    intro w
    by_cases h : w = v
    · subst w
      simp only [map_mul, map_add, map_one, quadraticEvaluate_localAdd_same,
        sub_add_cancel, a.inv_val]
    · simp [quadraticEvaluate_localAdd_other F d h]

@[simp] theorem quadraticEvaluate_localIdele_same (d : F) (v : ArchimedeanAdeles.Construction.Places F)
    (a : (ArchimedeanAdeles.Construction.localQuadratic F d v)ˣ) :
    ArchimedeanAdeles.Construction.quadraticEvaluate F d v (localIdeleElement F d v a).val = a.val := by
  simp [localIdeleElement]

@[simp] theorem quadraticEvaluate_localIdele_other (d : F) {v w : ArchimedeanAdeles.Construction.Places F}
    (h : w ≠ v) (a : (ArchimedeanAdeles.Construction.localQuadratic F d v)ˣ) :
    ArchimedeanAdeles.Construction.quadraticEvaluate F d w (localIdeleElement F d v a).val = 1 := by
  simp [localIdeleElement, h]

def localIdele (d : F) (v : ArchimedeanAdeles.Construction.Places F) :
    (ArchimedeanAdeles.Construction.localQuadratic F d v)ˣ →* (ArchimedeanAdeles.Construction.adelicQuadratic F d)ˣ where
  toFun := localIdeleElement F d v
  map_one' := by
    apply Units.ext
    simp [localIdeleElement]
  map_mul' a b := by
    apply Units.ext
    apply quadraticAdeles_ext F d
    intro w
    by_cases h : w = v
    · subst w
      simp
    · simp [h]

theorem localIdele_continuous (d : F) (v : ArchimedeanAdeles.Construction.Places F) : Continuous (localIdele F d v) := by
  apply Units.continuous_iff.mpr
  constructor
  · exact ((quadraticLocalAdd_continuous F d v).comp
      (Units.continuous_val.sub continuous_const)).add continuous_const
  · exact ((quadraticLocalAdd_continuous F d v).comp
      (Units.continuous_coe_inv.sub continuous_const)).add continuous_const

def localIdeleContinuous (d : F) (v : ArchimedeanAdeles.Construction.Places F) :
    (ArchimedeanAdeles.Construction.localQuadratic F d v)ˣ →ₜ* (ArchimedeanAdeles.Construction.adelicQuadratic F d)ˣ :=
  ⟨localIdele F d v, localIdele_continuous F d v⟩

def localCharacter (d : F) (χ : (ArchimedeanAdeles.Construction.adelicQuadratic F d)ˣ →ₜ* Circle) (v : ArchimedeanAdeles.Construction.Places F) :
    (ArchimedeanAdeles.Construction.localQuadratic F d v)ˣ →ₜ* Circle := χ.comp (localIdeleContinuous F d v)

/-- The local quadratic character, expressed by its norm criterion. At a
split place every unit is a norm, so this gives the trivial character. -/
def normCharacter (d : F) (v : ArchimedeanAdeles.Construction.Places F) (a : (ArchimedeanAdeles.Construction.Completion F v)ˣ) : Circle :=
  if ∃ b : (ArchimedeanAdeles.Construction.localQuadratic F d v)ˣ, Units.map QuadraticAlgebra.norm b = a then 1 else -1

def localScalarIdele (d : F) (v : ArchimedeanAdeles.Construction.Places F) :
    (ArchimedeanAdeles.Construction.Completion F v)ˣ →* (ArchimedeanAdeles.Construction.localQuadratic F d v)ˣ :=
  Units.map (algebraMap (ArchimedeanAdeles.Construction.Completion F v) (ArchimedeanAdeles.Construction.localQuadratic F d v)).toMonoidHom

/-- Actual prescribed Hecke characters. Only arithmetic character conditions
occur here: no local or global unitary splitting is a field. -/
structure GlobalCharacters (d : F) (n m : ℕ) where
  ψ : AddChar (ArchimedeanAdeles.Construction.Adeles F) ℂ
  ψ_continuous : Continuous ψ
  ψ_unitary : ∀ x, ‖ψ x‖ = 1
  ψ_nontrivial : ∃ x, ψ x ≠ 1
  ψ_principal : ∀ x : F, ψ (algebraMap F (ArchimedeanAdeles.Construction.Adeles F) x) = 1
  χV : (ArchimedeanAdeles.Construction.adelicQuadratic F d)ˣ →ₜ* Circle
  χW : (ArchimedeanAdeles.Construction.adelicQuadratic F d)ˣ →ₜ* Circle
  χV_principal : ∀ a : (UnitaryBase.Construction.Quadratic F d)ˣ,
    χV (Units.map (ArchimedeanAdeles.Construction.quadraticRational F d).toMonoidHom a) = 1
  χW_principal : ∀ a : (UnitaryBase.Construction.Quadratic F d)ˣ,
    χW (Units.map (ArchimedeanAdeles.Construction.quadraticRational F d).toMonoidHom a) = 1
  χV_restriction : ∀ v a,
    localCharacter F d χV v (localScalarIdele F d v a) = normCharacter F d v a ^ n
  χW_restriction : ∀ v a,
    localCharacter F d χW v (localScalarIdele F d v a) = normCharacter F d v a ^ m

end

end OAI.RepresentationTheory.Weil.AdelicSplitting.Characters.Construction
