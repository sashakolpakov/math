import OAI.RepresentationTheory.Weil.AdelicSplitting.Characters
import OAI.RepresentationTheory.Weil.AdelicSplitting.RestrictedLimits

/-! # Character Product -/

namespace OAI.RepresentationTheory.Weil.AdelicSplitting.CharacterProduct.Construction

noncomputable section

/-! Product formulas for the local components of the supplied global
characters, derived from convergence of actual adelic truncations. -/

open Filter
open scoped Classical _root_.NumberField _root_.Topology

variable (F : Type*) [Field F] [NumberField F]

theorem localAdd_hasSum (a : ArchimedeanAdeles.Construction.Adeles F) :
    HasSum (fun v => ArchimedeanAdeles.Construction.localAdd F v (ArchimedeanAdeles.Construction.evaluate F v a)) a := by
  have hei : (∑ v : NumberField.InfinitePlace F,
      ArchimedeanAdeles.Construction.localAdd F (Sum.inl v) (ArchimedeanAdeles.Construction.evaluate F (Sum.inl v) a)) = (a.1, 0) := by
    change (∑ v : NumberField.InfinitePlace F,
      (Pi.single v (a.1 v), (0 : ArchimedeanAdeles.Construction.FiniteAdeles F))) = (a.1, 0)
    rw [← prod_mk_sum, Finset.sum_const_zero]
    congr 1
    apply funext
    intro v
    rw [Finset.sum_apply]
    exact Fintype.sum_pi_single v a.1
  have hi : HasSum (fun v : NumberField.InfinitePlace F =>
      ArchimedeanAdeles.Construction.localAdd F (Sum.inl v) (ArchimedeanAdeles.Construction.evaluate F (Sum.inl v) a)) (a.1, 0) := by
    rw [← hei]
    exact hasSum_fintype _
  let inc : ArchimedeanAdeles.Construction.FiniteAdeles F →+ ArchimedeanAdeles.Construction.Adeles F :=
    { toFun := fun b => (0, b)
      map_zero' := rfl
      map_add' := fun b c => by
        change ((0 : NumberField.InfiniteAdeleRing F), b + c) = (0 + 0, b + c)
        rw [add_zero] }
  have hf := (RestrictedLimits.Construction.restricted_sum_single_hasSum
    (fun v : IsDedekindDomain.HeightOneSpectrum (𝓞 F) =>
      (v.adicCompletionIntegers F).toAddSubgroup) a.2).map inc
        (continuous_const.prodMk continuous_id)
  have hf' : HasSum (fun v : IsDedekindDomain.HeightOneSpectrum (𝓞 F) =>
      ArchimedeanAdeles.Construction.localAdd F (Sum.inr v) (ArchimedeanAdeles.Construction.evaluate F (Sum.inr v) a)) (0, a.2) := hf
  have h := HasSum.sum (f := fun v => ArchimedeanAdeles.Construction.localAdd F v (ArchimedeanAdeles.Construction.evaluate F v a)) hi hf'
  have he : ((a.1, 0) : ArchimedeanAdeles.Construction.Adeles F) + (0, a.2) = a := by
    change (a.1 + 0, 0 + a.2) = a
    rw [add_zero, zero_add]
    exact Prod.eta a
  convert h using 1
  exact he.symm

theorem quadraticLocalAdd_hasSum (d : F) (a : ArchimedeanAdeles.Construction.adelicQuadratic F d) :
    HasSum (fun v => Characters.Construction.quadraticLocalAdd F d v (ArchimedeanAdeles.Construction.quadraticEvaluate F d v a)) a := by
  let q : ArchimedeanAdeles.Construction.Adeles F × ArchimedeanAdeles.Construction.Adeles F →+ ArchimedeanAdeles.Construction.adelicQuadratic F d :=
    { toFun := fun x => ⟨x.1, x.2⟩
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  have hq : Continuous q := by
    rw [QuadraticTopology.Construction.quadratic_continuous_iff]
    exact ⟨continuous_fst, continuous_snd⟩
  exact ((localAdd_hasSum F a.re).prodMk (localAdd_hasSum F a.im)).map q hq

theorem localAdditiveCharacter_hasProd (ψ : AddChar (ArchimedeanAdeles.Construction.Adeles F) ℂ)
    (hψ : Continuous ψ) (a : ArchimedeanAdeles.Construction.Adeles F) :
    HasProd (fun v => Characters.Construction.localAdditiveCharacter F ψ v (ArchimedeanAdeles.Construction.evaluate F v a)) (ψ a) := by
  have h := (hψ.tendsto a).comp (localAdd_hasSum F a)
  change Tendsto (fun s : Finset (ArchimedeanAdeles.Construction.Places F) =>
    ∏ v ∈ s, Characters.Construction.localAdditiveCharacter F ψ v (ArchimedeanAdeles.Construction.evaluate F v a)) atTop (𝓝 (ψ a))
  convert h using 1
  · funext s
    induction s using Finset.induction_on with
    | empty => simp
    | @insert v s hv ih =>
        simp only [Finset.prod_insert hv, Finset.sum_insert hv, Function.comp_apply,
          ψ.map_add_eq_mul]
        exact congrArg (ψ (ArchimedeanAdeles.Construction.localAdd F v (ArchimedeanAdeles.Construction.evaluate F v a)) * ·) ih
  · rfl

theorem localAdditiveCharacter_principal_hasProd (ψ : AddChar (ArchimedeanAdeles.Construction.Adeles F) ℂ)
    (hψ : Continuous ψ) (hprincipal : ∀ a : F, ψ (algebraMap F (ArchimedeanAdeles.Construction.Adeles F) a) = 1)
    (a : F) : HasProd (fun v => Characters.Construction.localAdditiveCharacter F ψ v (ArchimedeanAdeles.Construction.rationalScalar F v a)) 1 := by
  have h := localAdditiveCharacter_hasProd F ψ hψ (algebraMap F (ArchimedeanAdeles.Construction.Adeles F) a)
  rw [hprincipal] at h
  exact h

def localizeIdele (d : F) (a : (ArchimedeanAdeles.Construction.adelicQuadratic F d)ˣ) (v : ArchimedeanAdeles.Construction.Places F) :
    (ArchimedeanAdeles.Construction.localQuadratic F d v)ˣ :=
  Units.map (ArchimedeanAdeles.Construction.quadraticEvaluate F d v).toMonoidHom a

theorem localIdele_product_val (d : F) (a : (ArchimedeanAdeles.Construction.adelicQuadratic F d)ˣ)
    (s : Finset (ArchimedeanAdeles.Construction.Places F)) :
    (∏ v ∈ s, Characters.Construction.localIdele F d v (localizeIdele F d a v)).val =
      (∑ v ∈ s, Characters.Construction.quadraticLocalAdd F d v (ArchimedeanAdeles.Construction.quadraticEvaluate F d v (a.val - 1))) + 1 := by
  apply Characters.Construction.quadraticAdeles_ext F d
  intro w
  simp only [Units.coe_prod, map_prod, map_add, map_sum, map_one]
  by_cases hw : w ∈ s
  · rw [Finset.prod_eq_single w, Finset.sum_eq_single w]
    · simp [Characters.Construction.localIdele, localizeIdele]
    · intro v _ hv
      exact Characters.Construction.quadraticEvaluate_localAdd_other F d hv.symm _
    · exact fun h => (h hw).elim
    · intro v _ hv
      exact Characters.Construction.quadraticEvaluate_localIdele_other F d hv.symm _
    · exact fun h => (h hw).elim
  · rw [Finset.prod_eq_one, Finset.sum_eq_zero, zero_add]
    · intro v hv
      exact Characters.Construction.quadraticEvaluate_localAdd_other F d (show w ≠ v from fun h => hw (h.symm ▸ hv)) _
    · intro v hv
      exact Characters.Construction.quadraticEvaluate_localIdele_other F d (show w ≠ v from fun h => hw (h.symm ▸ hv)) _

theorem localIdele_product_val_tendsto (d : F) (a : (ArchimedeanAdeles.Construction.adelicQuadratic F d)ˣ) :
    Tendsto (fun s : Finset (ArchimedeanAdeles.Construction.Places F) =>
      (∏ v ∈ s, Characters.Construction.localIdele F d v (localizeIdele F d a v)).val) atTop (𝓝 a.val) := by
  simp only [localIdele_product_val]
  have h := (quadraticLocalAdd_hasSum F d (a.val - 1)).add_const 1
  rw [sub_add_cancel] at h
  exact h

theorem localIdele_hasProd (d : F) (a : (ArchimedeanAdeles.Construction.adelicQuadratic F d)ˣ) :
    HasProd (fun v => Characters.Construction.localIdele F d v (localizeIdele F d a v)) a := by
  apply Units.isEmbedding_embedProduct.tendsto_nhds_iff.mpr
  have hv := localIdele_product_val_tendsto F d a
  have hi := localIdele_product_val_tendsto F d a⁻¹
  have hinv : Tendsto (fun s : Finset (ArchimedeanAdeles.Construction.Places F) =>
      ((∏ v ∈ s, Characters.Construction.localIdele F d v (localizeIdele F d a v))⁻¹).val)
      atTop (𝓝 (a⁻¹).val) := by
    simpa only [mul_inv_rev, Finset.prod_inv_distrib, localizeIdele, map_inv] using hi
  exact hv.prodMk_nhds ((MulOpposite.continuous_op.tendsto _).comp hinv)

theorem localCharacter_hasProd (d : F) (χ : (ArchimedeanAdeles.Construction.adelicQuadratic F d)ˣ →ₜ* Circle)
    (a : (ArchimedeanAdeles.Construction.adelicQuadratic F d)ˣ) :
    HasProd (fun v => Characters.Construction.localCharacter F d χ v (localizeIdele F d a v)) (χ a) :=
  (localIdele_hasProd F d a).map χ χ.continuous

theorem localCharacter_principal_hasProd (d : F)
    (χ : (ArchimedeanAdeles.Construction.adelicQuadratic F d)ˣ →ₜ* Circle)
    (hχ : ∀ a : (UnitaryBase.Construction.Quadratic F d)ˣ,
      χ (Units.map (ArchimedeanAdeles.Construction.quadraticRational F d).toMonoidHom a) = 1)
    (a : (UnitaryBase.Construction.Quadratic F d)ˣ) :
    HasProd (fun v => Characters.Construction.localCharacter F d χ v
      (Units.map (UnitaryBase.Construction.quadraticBaseChange (ArchimedeanAdeles.Construction.rationalScalar F v) d).toMonoidHom a)) 1 := by
  have h := localCharacter_hasProd F d χ (Units.map (ArchimedeanAdeles.Construction.quadraticRational F d).toMonoidHom a)
  rw [hχ] at h
  exact h

theorem globalCharacters_chiV_hasProd (d : F) (n m : ℕ)
    (C : Characters.Construction.GlobalCharacters F d n m) (a : (UnitaryBase.Construction.Quadratic F d)ˣ) :
    HasProd (fun v => Characters.Construction.localCharacter F d C.χV v
      (Units.map (UnitaryBase.Construction.quadraticBaseChange (ArchimedeanAdeles.Construction.rationalScalar F v) d).toMonoidHom a)) 1 :=
  localCharacter_principal_hasProd F d C.χV C.χV_principal a

theorem globalCharacters_chiW_hasProd (d : F) (n m : ℕ)
    (C : Characters.Construction.GlobalCharacters F d n m) (a : (UnitaryBase.Construction.Quadratic F d)ˣ) :
    HasProd (fun v => Characters.Construction.localCharacter F d C.χW v
      (Units.map (UnitaryBase.Construction.quadraticBaseChange (ArchimedeanAdeles.Construction.rationalScalar F v) d).toMonoidHom a)) 1 :=
  localCharacter_principal_hasProd F d C.χW C.χW_principal a

theorem normCharacter_power_principal_hasProd (d : F) (e : ℕ)
    (χ : (ArchimedeanAdeles.Construction.adelicQuadratic F d)ˣ →ₜ* Circle)
    (hχ : ∀ a : (UnitaryBase.Construction.Quadratic F d)ˣ,
      χ (Units.map (ArchimedeanAdeles.Construction.quadraticRational F d).toMonoidHom a) = 1)
    (hres : ∀ v a, Characters.Construction.localCharacter F d χ v (Characters.Construction.localScalarIdele F d v a) =
      Characters.Construction.normCharacter F d v a ^ e) (a : Fˣ) :
    HasProd (fun v => Characters.Construction.normCharacter F d v
      (Units.map (ArchimedeanAdeles.Construction.rationalScalar F v).toMonoidHom a) ^ e) 1 := by
  have h := localCharacter_principal_hasProd F d χ hχ
    (Units.map (algebraMap F (UnitaryBase.Construction.Quadratic F d)).toMonoidHom a)
  apply h.congr_fun
  intro v
  have he : Units.map (UnitaryBase.Construction.quadraticBaseChange (ArchimedeanAdeles.Construction.rationalScalar F v) d).toMonoidHom
      (Units.map (algebraMap F (UnitaryBase.Construction.Quadratic F d)).toMonoidHom a) =
      Characters.Construction.localScalarIdele F d v (Units.map (ArchimedeanAdeles.Construction.rationalScalar F v).toMonoidHom a) := by
    apply Units.ext
    apply QuadraticAlgebra.ext
    · rfl
    · exact map_zero (ArchimedeanAdeles.Construction.rationalScalar F v)
  rw [he]
  exact (hres v _).symm

theorem globalCharacters_norm_n_hasProd (d : F) (n m : ℕ)
    (C : Characters.Construction.GlobalCharacters F d n m) (a : Fˣ) :
    HasProd (fun v => Characters.Construction.normCharacter F d v
      (Units.map (ArchimedeanAdeles.Construction.rationalScalar F v).toMonoidHom a) ^ n) 1 :=
  normCharacter_power_principal_hasProd F d n C.χV C.χV_principal C.χV_restriction a

theorem globalCharacters_norm_m_hasProd (d : F) (n m : ℕ)
    (C : Characters.Construction.GlobalCharacters F d n m) (a : Fˣ) :
    HasProd (fun v => Characters.Construction.normCharacter F d v
      (Units.map (ArchimedeanAdeles.Construction.rationalScalar F v).toMonoidHom a) ^ m) 1 :=
  normCharacter_power_principal_hasProd F d m C.χW C.χW_principal C.χW_restriction a

end

end OAI.RepresentationTheory.Weil.AdelicSplitting.CharacterProduct.Construction
