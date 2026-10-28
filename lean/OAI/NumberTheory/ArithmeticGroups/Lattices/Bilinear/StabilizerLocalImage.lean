import OAI.NumberTheory.ArithmeticGroups.Lattices.Lie.AutomorphismTransversal
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv
import Mathlib.Analysis.Calculus.FDeriv.Mul

/-! # Stabilizer Local Image -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.Bilinear.StabilizerLocalImage.Construction

noncomputable section

section

/-! A differentiable family of automorphisms whose derivative is exactly
the derivation space contains a neighborhood of the identity in the full
bilinear-operation stabilizer. -/

open scoped Classical _root_.Topology RightActions
open Filter Set

theorem hasStrictFDerivAt_product_slice
    {E F A : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedRing A] [NormedAlgebra ℝ A]
    (f : E → A) (a : E →L[ℝ] A) (b : F →L[ℝ] A)
    (hf0 : f 0 = 1) (hf : HasStrictFDerivAt f a 0) :
    HasStrictFDerivAt (fun p : E × F => f p.1 * (1 + b p.2)) (a.coprod b) 0 := by
  have hfP : HasStrictFDerivAt (fun p : E × F => f p.1)
      (a.comp (ContinuousLinearMap.fst ℝ E F)) 0 := by
    exact HasStrictFDerivAt.comp (0 : E × F)
      (f := ContinuousLinearMap.fst ℝ E F) (g := f) hf
      (ContinuousLinearMap.fst ℝ E F).hasStrictFDerivAt
  have hbP : HasStrictFDerivAt (fun p : E × F => 1 + b p.2)
      (b.comp (ContinuousLinearMap.snd ℝ E F)) 0 := by
    exact HasStrictFDerivAt.const_add (1 : A)
      (f := b.comp (ContinuousLinearMap.snd ℝ E F))
      (f' := b.comp (ContinuousLinearMap.snd ℝ E F)) (x := (0 : E × F))
      (b.comp (ContinuousLinearMap.snd ℝ E F)).hasStrictFDerivAt
  convert! hfP.mul' hbP using 1
  apply ContinuousLinearMap.ext
  intro p
  change a p.1 + b p.2 = f 0 * b p.2 + a p.1 * (1 + b 0)
  simp [hf0, add_comm]

theorem bilinear_stabilizer_local_image
    {E L : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup L] [NormedSpace ℝ L] [FiniteDimensional ℝ L]
    (B : L →L[ℝ] L →L[ℝ] L) (f : E → (L →L[ℝ] L)) (a : E →L[ℝ] (L →L[ℝ] L))
    (hf0 : f 0 = 1) (hf : HasStrictFDerivAt f a 0)
    (ha : Function.Injective a)
    (hrange : LinearMap.range a.toLinearMap =
      LinearMap.ker (Lie.AutomorphismTransversal.Construction.continuousBilinearDerivationDefect B).toLinearMap)
    (hfinj : ∀ x, Function.Injective (f x))
    (hpres : ∀ p x y, f p (B x y) = B (f p x) (f p y)) :
    ∀ᶠ T in 𝓝 (1 : L →L[ℝ] L),
      (∀ x y, T (B x y) = B (T x) (T y)) → T ∈ Set.range f := by
  let : NormedAddCommGroup (L →L[ℝ] L) := inferInstance
  let : NormedSpace ℝ (L →L[ℝ] L) := inferInstance
  let : FiniteDimensional ℝ (L →L[ℝ] L) := inferInstance
  let : NormedAddCommGroup (L →L[ℝ] L →L[ℝ] L) := inferInstance
  let : NormedSpace ℝ (L →L[ℝ] L →L[ℝ] L) := inferInstance
  obtain ⟨W, hW⟩ := (LinearMap.range a.toLinearMap).exists_isCompl
  have hdisj : Disjoint W (LinearMap.ker (Lie.AutomorphismTransversal.Construction.continuousBilinearDerivationDefect B).toLinearMap) := by
    rw [← hrange]
    exact hW.disjoint.symm
  obtain ⟨ε, hε, hisolated⟩ := Lie.AutomorphismTransversal.Construction.bilinear_stabilizer_transversal_isolated B W hdisj
  let e : (E × W) ≃L[ℝ] (L →L[ℝ] L) :=
    (((LinearEquiv.ofInjective a.toLinearMap ha).prodCongr (LinearEquiv.refl ℝ W)).trans
      (Submodule.prodEquivOfIsCompl _ W hW)).toContinuousLinearEquiv
  have he (p : E × W) : e p = a p.1 + (p.2 : L →L[ℝ] L) := rfl
  let s : (E × W) →L[ℝ] (L →L[ℝ] L) :=
    W.subtypeL.comp (ContinuousLinearMap.snd ℝ E W)
  let P : E × W → (L →L[ℝ] L) := fun p => f p.1 * (1 + (p.2 : L →L[ℝ] L))
  have hP0 : P 0 = 1 := by simp [P, hf0]
  have hP : HasStrictFDerivAt P (e : (E × W) →L[ℝ] (L →L[ℝ] L)) 0 := by
    have heq : (e : (E × W) →L[ℝ] (L →L[ℝ] L)) = a.coprod W.subtypeL := by
      apply ContinuousLinearMap.ext
      intro p
      exact he p
    rw [heq]
    exact hasStrictFDerivAt_product_slice f a W.subtypeL hf0 hf
  let : CompleteSpace E := FiniteDimensional.complete ℝ E
  let : CompleteSpace L := FiniteDimensional.complete ℝ L
  let : CompleteSpace W := FiniteDimensional.complete ℝ W
  have hsmall : {p : E × W | ‖(p.2 : L →L[ℝ] L)‖ < ε} ∈ 𝓝 0 := by
    have ho : IsOpen {p : E × W | ‖(p.2 : L →L[ℝ] L)‖ < ε} :=
      isOpen_lt s.continuous.norm continuous_const
    exact ho.mem_nhds (by simpa using hε)
  have himage : P '' {p : E × W | ‖(p.2 : L →L[ℝ] L)‖ < ε} ∈ 𝓝 1 := by
    rw [← hP0, ← hP.map_nhds_eq_of_equiv (f' := e)]
    exact Filter.image_mem_map hsmall
  filter_upwards [himage] with T hT
  intro hTB
  obtain ⟨⟨p, q⟩, hq, rfl⟩ := hT
  have hqB : ∀ x y, (ContinuousLinearMap.id ℝ L + (q : L →L[ℝ] L)) (B x y) =
      B ((ContinuousLinearMap.id ℝ L + (q : L →L[ℝ] L)) x)
        ((ContinuousLinearMap.id ℝ L + (q : L →L[ℝ] L)) y) := by
    intro x y
    apply hfinj p
    rw [hpres]
    exact hTB x y
  have hq0 := hisolated q q.property hq hqB
  exact ⟨p, by simp [P, hq0]⟩

end

/-! A parameterized bracket automorphism family locally covers the
stabilizer whenever its derivative spans the derivations. -/

open scoped _root_.Topology
open Filter Set

theorem bilinear_stabilizer_local_image_of_range
    {E L : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup L] [NormedSpace ℝ L] [FiniteDimensional ℝ L]
    (B : L →L[ℝ] L →L[ℝ] L) (f : E → (L →L[ℝ] L)) (a : E →L[ℝ] (L →L[ℝ] L))
    (hf0 : f 0 = 1) (hf : HasStrictFDerivAt f a 0)
    (hrange : LinearMap.range a.toLinearMap =
      LinearMap.ker (Lie.AutomorphismTransversal.Construction.continuousBilinearDerivationDefect B).toLinearMap)
    (hfinj : ∀ x, Function.Injective (f x))
    (hpres : ∀ p x y, f p (B x y) = B (f p x) (f p y)) :
    ∀ᶠ T in 𝓝 (1 : L →L[ℝ] L),
      (∀ x y, T (B x y) = B (T x) (T y)) → T ∈ Set.range f := by
  obtain ⟨W, hW⟩ := a.toLinearMap.ker.exists_isCompl
  let a' := a.comp W.subtypeL
  have hi : Function.Injective a' := by
    apply (injective_iff_map_eq_zero a').mpr
    intro x hx
    apply Subtype.ext
    exact Submodule.disjoint_def.mp hW.disjoint x.val hx x.property
  have hr : a'.toLinearMap.range = a.toLinearMap.range := by
    apply le_antisymm
    · rintro _ ⟨x, rfl⟩
      exact ⟨x.val, rfl⟩
    · rintro _ ⟨x, rfl⟩
      have hx : x ∈ a.toLinearMap.ker ⊔ W := by rw [hW.sup_eq_top]; trivial
      obtain ⟨u, hu, v, hv, huv⟩ := Submodule.mem_sup.mp hx
      refine ⟨⟨v, hv⟩, ?_⟩
      change a v = a x
      rw [← huv, map_add, show a u = 0 from hu, zero_add]
  have hd : HasStrictFDerivAt (fun x : W => f x.val) a' 0 := by
    convert! hf.comp (0 : W) W.subtypeL.hasStrictFDerivAt using 1
  have h := bilinear_stabilizer_local_image B (fun x : W => f x.val) a' hf0 hd hi
    (hr.trans hrange) (fun x => hfinj x.val) (fun p => hpres p.val)
  filter_upwards [h] with T hT
  intro hB
  obtain ⟨p, hp⟩ := hT hB
  exact ⟨p.val, hp⟩

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.Bilinear.StabilizerLocalImage.Construction
