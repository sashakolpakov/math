import OAI.RepresentationTheory.Weil.AdelicSplitting.ArchimedeanPositionChart
import OAI.RepresentationTheory.Weil.AdelicSplitting.ArchimedeanDualLattice
import OAI.RepresentationTheory.Weil.AdelicSplitting.CharacterProduct

/-! # Archimedean Position Pairing -/

namespace OAI.RepresentationTheory.Weil.AdelicSplitting.ArchimedeanPositionPairing.Construction

noncomputable section

/-! The Minkowski position chart is additive, and its bilinear character
pairing is exactly the product of the actual archimedean local phases. -/

open scoped Classical _root_.NumberField
open _root_.NumberField

variable (F : Type) [Field F] [NumberField F] (N : ℕ)

def archimedeanPositionAddChart :
    (∀ v : InfinitePlace F, Local.FunctionsMetaplectic.Construction.Position v.Completion N) ≃ₜ+ (Fin N → mixedEmbedding.mixedSpace F) where
  __ := ArchimedeanPositionChart.Construction.archimedeanPositionChart F N
  map_add' x y := by
    funext i
    exact (InfiniteAdeleRing.ringEquiv_mixedSpace F).map_add (fun v => x v i) (fun v => y v i)

theorem archimedeanCharacter_infinite_product (ψ : AddChar (ArchimedeanAdeles.Construction.Adeles F) ℂ) (hc : Continuous ψ)
    (x : InfiniteAdeleRing F) :
    ArchimedeanCharacterLattice.Construction.archimedeanCharacter F ψ (ArchimedeanAdeles.Construction.infiniteAdeleMixedHomeomorph F x) =
      ∏ v : InfinitePlace F, Characters.Construction.localAdditiveCharacter F ψ (.inl v) (x v) := by
  let a : ArchimedeanAdeles.Construction.Adeles F := (x, 0)
  let f := fun v : ArchimedeanAdeles.Construction.Places F => Characters.Construction.localAdditiveCharacter F ψ v (ArchimedeanAdeles.Construction.evaluate F v a)
  have hh : HasProd f (ψ a) := CharacterProduct.Construction.localAdditiveCharacter_hasProd F ψ hc a
  have hout : ∀ v ∉ Set.range (Sum.inl : InfinitePlace F → ArchimedeanAdeles.Construction.Places F), f v = 1 := by
    intro v hv
    cases v with
    | inl v => exact (hv ⟨v, rfl⟩).elim
    | inr v => exact AddChar.map_zero_eq_one _
  have hp : HasProd (fun v : InfinitePlace F => Characters.Construction.localAdditiveCharacter F ψ (.inl v) (x v)) (ψ a) :=
    (Sum.inl_injective.hasProd_iff hout).mpr hh
  have he : ArchimedeanCharacterLattice.Construction.mixedAdelicAdd F (ArchimedeanAdeles.Construction.infiniteAdeleMixedHomeomorph F x) = a := by
    apply Prod.ext
    · exact (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm_apply_apply x
    · rfl
  change ψ (ArchimedeanCharacterLattice.Construction.mixedAdelicAdd F (ArchimedeanAdeles.Construction.infiniteAdeleMixedHomeomorph F x)) = _
  rw [he]
  exact hp.unique (hasProd_fintype _)

def mixedPositionPairing (L : mixedEmbedding.mixedSpace F →ₗ[ℝ] ℝ) :
    LinearMap.BilinForm ℝ (Fin N → mixedEmbedding.mixedSpace F) where
  toFun x :=
    { toFun y := L (∑ i, x i * y i)
      map_add' y z := by simp [mul_add, Finset.sum_add_distrib]
      map_smul' c y := by simp [← Finset.smul_sum] }
  map_add' x y := by
    apply LinearMap.ext
    intro z
    change L (∑ i, (x + y) i * z i) = L (∑ i, x i * z i) + L (∑ i, y i * z i)
    simp [add_mul, Finset.sum_add_distrib]
  map_smul' c x := by
    apply LinearMap.ext
    intro y
    change L (∑ i, (c • x) i * y i) = c • L (∑ i, x i * y i)
    simp [← Finset.smul_sum]

omit [NumberField F] in
theorem mixedPositionPairing_apply (L : mixedEmbedding.mixedSpace F →ₗ[ℝ] ℝ)
    (x y : Fin N → mixedEmbedding.mixedSpace F) :
    mixedPositionPairing F N L x y = L (∑ i, x i * y i) := rfl

omit [NumberField F] in
theorem mixedPositionPairing_separating (L : mixedEmbedding.mixedSpace F →ₗ[ℝ] ℝ)
    (hL : ∀ x : mixedEmbedding.mixedSpace F, (∀ y, L (x * y) = 0) → x = 0) :
    (mixedPositionPairing F N L).SeparatingLeft := by
  intro x hx
  funext i
  apply hL (x i)
  intro y
  have h := hx (Pi.single i y)
  simpa [mixedPositionPairing_apply, Pi.single_apply] using h

theorem archimedeanPosition_dot_phase (ψ : AddChar (ArchimedeanAdeles.Construction.Adeles F) ℂ) (hc : Continuous ψ)
    (x y : ∀ v : InfinitePlace F, Local.FunctionsMetaplectic.Construction.Position v.Completion N) :
    ArchimedeanCharacterLattice.Construction.archimedeanCharacter F ψ (-(∑ i, ArchimedeanPositionChart.Construction.archimedeanPositionChart F N x i * ArchimedeanPositionChart.Construction.archimedeanPositionChart F N y i)) =
      ∏ v : InfinitePlace F, Characters.Construction.localAdditiveCharacter F ψ (.inl v) (-Local.FunctionsMetaplectic.Construction.dot (x v) (y v)) := by
  let e := InfiniteAdeleRing.ringEquiv_mixedSpace F
  have he : -(∑ i, ArchimedeanPositionChart.Construction.archimedeanPositionChart F N x i * ArchimedeanPositionChart.Construction.archimedeanPositionChart F N y i) =
      ArchimedeanAdeles.Construction.infiniteAdeleMixedHomeomorph F (fun v => -Local.FunctionsMetaplectic.Construction.dot (x v) (y v)) := by
    apply e.symm.injective
    change e.symm (-(∑ i, e (fun v => x v i) * e (fun v => y v i))) =
      e.symm (e (fun v => -Local.FunctionsMetaplectic.Construction.dot (x v) (y v)))
    simp only [map_neg, map_sum, map_mul]
    change -(∑ i, e.symm (e (fun v => x v i)) * e.symm (e (fun v => y v i))) =
      e.symm (e (fun v => -Local.FunctionsMetaplectic.Construction.dot (x v) (y v)))
    let X (i : Fin N) : InfiniteAdeleRing F := fun v => x v i
    let Y (i : Fin N) : InfiniteAdeleRing F := fun v => y v i
    let Z : InfiniteAdeleRing F := fun v => -Local.FunctionsMetaplectic.Construction.dot (x v) (y v)
    change -(∑ i, e.symm (e (X i)) * e.symm (e (Y i))) = e.symm (e Z)
    have hX (i : Fin N) : e.symm (e (X i)) = X i := e.symm_apply_apply _
    have hY (i : Fin N) : e.symm (e (Y i)) = Y i := e.symm_apply_apply _
    have hZ : e.symm (e Z) = Z := e.symm_apply_apply _
    simp only [hX, hY, hZ]
    funext v
    change -(∑ i, X i * Y i) v = -Local.FunctionsMetaplectic.Construction.dot (x v) (y v)
    let ev : InfiniteAdeleRing F →+* v.Completion := Pi.evalRingHom (fun w : InfinitePlace F => w.Completion) v
    have hv : ev (∑ i, X i * Y i) = ∑ i, ev (X i) * ev (Y i) := by
      simp only [map_sum, map_mul]
    exact congrArg Neg.neg hv
  rw [he]
  exact archimedeanCharacter_infinite_product F ψ hc _

end

end OAI.RepresentationTheory.Weil.AdelicSplitting.ArchimedeanPositionPairing.Construction
