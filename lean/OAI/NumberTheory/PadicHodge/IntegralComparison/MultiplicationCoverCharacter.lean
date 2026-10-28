import OAI.NumberTheory.PadicHodge.IntegralComparison.Finite.CoverCharacter
import OAI.NumberTheory.PadicHodge.IntegralComparison.FiniteCoefficient.GroupLaw
import OAI.NumberTheory.PadicHodge.IntegralComparison.MultiplicationKernelPair
import OAI.AlgebraicGeometry.FormalGeometry.Completion.Multiplication

/-! # Multiplication Cover Character -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.MultiplicationCoverCharacter

noncomputable section

/-! The actual multiplication cover gives an additive injective character
of finite-coefficient H¹ on its scheme-theoretic torsion overlap. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite
open MonoidalCategory CartesianMonoidalCategory MonObj

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open OAI.AlgebraicGeometry.FormalGeometry.Completion.Multiplication.Construction

universe u
variable (ℓ n : ℕ) [Fact ℓ.Prime]
  {k : Type u} [Field k] [IsAlgClosed k]
  (A : Over (Spec (.of k))) [GrpObj A] [IsCommMonObj A]
  [Smooth A.hom] [IsProper A.hom] [GeometricallyIntegral A.hom]
  (hℓ : (ℓ : k) ≠ 0)

local notation "m" => (Over.Hom.left ((𝟙 A : A ⟶ A) ^ (ℓ ^ n)))

include hℓ

omit [Fact (Nat.Prime ℓ)] [IsAlgClosed k] [IsProper A.hom] [GeometricallyIntegral A.hom] in
theorem multiplicationEtale : Etale m := AlgebraicGeometry.FormalGeometry.Completion.Multiplication.Construction.multiplication_etale A (ℓ ^ n)
  (by rw [Nat.cast_pow]; exact pow_ne_zero n hℓ)

abbrev cover : A.left.ProEt := by
  let : Etale m := multiplicationEtale ℓ n A hℓ
  exact Scheme.ProEt.mk m

abbrev overlap : A.left.ProEt := by
  let : Etale m := multiplicationEtale ℓ n A hℓ
  exact Scheme.ProEt.mk (pullback.fst m m ≫ m)

def first : overlap ℓ n A hℓ ⟶ cover ℓ n A hℓ :=
  MorphismProperty.Over.homMk (pullback.fst m m) rfl

def second : overlap ℓ n A hℓ ⟶ cover ℓ n A hℓ :=
  MorphismProperty.Over.homMk (pullback.snd m m) (pullback.condition.symm)

local instance cover_preconnected : PreconnectedSpace (cover ℓ n A hℓ).left := by
  let : IsIntegral A.left := GeometricallyIntegral.isIntegral_of_subsingleton A.hom
  exact inferInstanceAs (PreconnectedSpace A.left)

def character : (AlgebraicGeometry.FormalGeometry.Completion.Finite.CoefficientSheaf.Construction.finiteEllAdicCoefficient ℓ n A.left).H 1 →+
    (AlgebraicGeometry.FormalGeometry.Completion.Finite.CoefficientSheaf.Construction.finiteEllAdicCoefficient ℓ n A.left).obj.obj (op (overlap ℓ n A hℓ)) :=
  Finite.CoverCharacter.character ℓ n (cover ℓ n A hℓ) (overlap ℓ n A hℓ)
    (first ℓ n A hℓ) (second ℓ n A hℓ)
    (FiniteCoefficient.GroupLaw.multiplication_pow_pullback_zero ℓ n A)

theorem character_injective : Function.Injective (character ℓ n A hℓ) := by
  let U := cover ℓ n A hℓ
  let D := overlap ℓ n A hℓ
  let a := first ℓ n A hℓ
  let b := second ℓ n A hℓ
  let e : (⊤_ A.left.ProEt) ≅ Scheme.ProEt.mk (𝟙 A.left) :=
    terminalIsTerminal.uniqueUpToIso (AlgebraicGeometry.FormalGeometry.Completion.FiniteTorsor.GlobalSections.Construction.proEtaleIdentityIsTerminal A.left)
  let e' := ((Scheme.ProEt.forget A.left) ⋙ Over.forget A.left).mapIso e
  have he : e'.hom = (⊤_ A.left.ProEt).hom := by
    exact (Category.comp_id e.hom.left).symm.trans (MorphismProperty.Over.w e.hom)
  let : IsIso (⊤_ A.left.ProEt).hom := he ▸ inferInstanceAs (IsIso e'.hom)
  let f := terminal.from U
  have hf : f.left = U.hom ≫ inv (⊤_ A.left.ProEt).hom := by
    apply (cancel_mono (⊤_ A.left.ProEt).hom).1
    simp only [Category.assoc, IsIso.inv_hom_id, Category.comp_id]
    exact MorphismProperty.Over.w f
  have hn : ((ℓ ^ n : ℕ) : k) ≠ 0 := by rw [Nat.cast_pow]; exact pow_ne_zero n hℓ
  let : IsFinite U.hom := AlgebraicGeometry.FormalGeometry.Completion.Multiplication.Construction.multiplication_isFinite A (ℓ ^ n) hn
  let : Surjective U.hom := AlgebraicGeometry.FormalGeometry.Completion.Multiplication.Construction.multiplication_surjective A (ℓ ^ n) hn
  let : IsFinite f.left := by rw [hf]; infer_instance
  let : Surjective f.left := by rw [hf]; infer_instance
  have hD : IsPullback a.left b.left f.left f.left := by
    change IsPullback (pullback.fst m m) (pullback.snd m m) f.left f.left
    refine (IsPullback.of_hasPullback m m).of_iso' (Iso.refl _) (Iso.refl _) (Iso.refl _) e'
      (by simp only [Iso.refl_hom, Category.id_comp, Category.comp_id])
      (by simp only [Iso.refl_hom, Category.id_comp, Category.comp_id]) ?_ ?_
    · change 𝟙 A.left ≫ m = f.left ≫ e'.hom
      rw [Category.id_comp, he]
      exact (MorphismProperty.Over.w f).symm
    · change 𝟙 A.left ≫ m = f.left ≫ e'.hom
      rw [Category.id_comp, he]
      exact (MorphismProperty.Over.w f).symm
  exact Finite.CoverCharacter.character_injective ℓ n U D a b
    (FiniteCoefficient.GroupLaw.multiplication_pow_pullback_zero ℓ n A) hD

def productCharacter : (AlgebraicGeometry.FormalGeometry.Completion.Finite.CoefficientSheaf.Construction.finiteEllAdicCoefficient ℓ n A.left).H 1 →+
    C((A ⊗ AlgebraicGeometry.AbelianScheme.TorsionQuotient.SubgroupFunctor.torsionScheme A (ℓ ^ n)).left, ZMod (ℓ ^ n)) where
  toFun x := (character ℓ n A hℓ x).down.comp
    ⟨(MultiplicationKernelPair.schemeEquiv A (ℓ ^ n)).hom,
      (MultiplicationKernelPair.schemeEquiv A (ℓ ^ n)).hom.continuous⟩
  map_zero' := by
    rw [map_zero]
    rfl
  map_add' x y := by
    rw [map_add]
    rfl

theorem productCharacter_injective : Function.Injective (productCharacter ℓ n A hℓ) := by
  intro x y hxy
  apply character_injective ℓ n A hℓ
  apply ULift.ext
  apply ContinuousMap.ext
  intro z
  obtain ⟨w, rfl⟩ := (MultiplicationKernelPair.schemeEquiv A (ℓ ^ n)).hom.surjective z
  exact congrArg (fun f : C((A ⊗ AlgebraicGeometry.AbelianScheme.TorsionQuotient.SubgroupFunctor.torsionScheme A (ℓ ^ n)).left, ZMod (ℓ ^ n)) => f w) hxy

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.MultiplicationCoverCharacter
