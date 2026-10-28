import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.BaseChange
import OAI.AlgebraicGeometry.Picard.Homomorphisms.Kernel
import Mathlib.CategoryTheory.Sites.Subcanonical

/-! # Quotient -/

namespace OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.Quotient.Construction

noncomputable section

/-!
The independently constructed subgroup quotient is identified with the
target of relative Frobenius using Homomorphisms as an explicit named input. The
input is the fppf universal property from the Homomorphisms specification, formulated
on all test schemes. No equality of quotient objects is assumed.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

universe u

variable {S : Scheme.{u}} {A AF : Over S} [GrpObj A] [GrpObj AF]

/-- Homomorphisms's quotient property gives descent for maps of sheaves. -/
theorem kernelQuotient_desc_of_Homomorphisms
    (F : A ⟶ AF) [IsMonHom F]
    (h_Homomorphisms : Picard.Homomorphisms.Quotient.Construction.IsFppfQuotientByKernel F)
    (P : BaseChange.Construction.FppfSheaves S) (a : (BaseChange.Construction.fppfPoints S).obj A ⟶ P)
    (ha :
      (BaseChange.Construction.fppfPoints S).map
          ((fst (Picard.Homomorphisms.Kernel.Construction.kernelScheme F) A ≫ Picard.Homomorphisms.Kernel.Construction.kernelInclusion F) *
            snd (Picard.Homomorphisms.Kernel.Construction.kernelScheme F) A) ≫ a =
        (BaseChange.Construction.fppfPoints S).map (snd (Picard.Homomorphisms.Kernel.Construction.kernelScheme F) A) ≫ a) :
    ∃! b : (BaseChange.Construction.fppfPoints S).obj AF ⟶ P,
      (BaseChange.Construction.fppfPoints S).map F ≫ b = a := by
  let J := Scheme.fppfTopology.over S
  let x := J.uliftYonedaEquiv a
  have hinv : ∀ (T : Over S) (y : T ⟶ A) (k : Picard.Homomorphisms.Quotient.Construction.kernelPoints F T),
      P.obj.map ((k.val * y).op) x = P.obj.map y.op x := by
    intro T y k
    obtain ⟨j, hj, _⟩ := (Picard.Homomorphisms.Kernel.Construction.kernelScheme_universal F T k.val).mp k.property
    let t := lift j y
    have hact : t ≫
        ((fst (Picard.Homomorphisms.Kernel.Construction.kernelScheme F) A ≫ Picard.Homomorphisms.Kernel.Construction.kernelInclusion F) *
          snd (Picard.Homomorphisms.Kernel.Construction.kernelScheme F) A) = k.val * y := by
      simp only [t, MonObj.comp_mul, ← Category.assoc,
        lift_fst, lift_snd, hj]
    have hproj : t ≫ snd (Picard.Homomorphisms.Kernel.Construction.kernelScheme F) A = y := lift_snd _ _
    have h := congrArg (fun b => (BaseChange.Construction.fppfPoints S).map t ≫ b) ha
    simp only [← Category.assoc, ← Functor.map_comp, hact, hproj] at h
    exact (J.uliftYonedaEquiv_naturality a (k.val * y)).trans
      ((congrArg J.uliftYonedaEquiv h).trans
        (J.uliftYonedaEquiv_naturality a y).symm)
  obtain ⟨b, hb, huniq⟩ := h_Homomorphisms P.obj ((isSheaf_iff_isSheaf_of_type _ _).mp P.property)
    x hinv
  refine ⟨J.uliftYonedaEquiv.symm b, ?_, ?_⟩
  · apply J.uliftYonedaEquiv.injective
    rw [← J.uliftYonedaEquiv_naturality, Equiv.apply_symm_apply]
    exact hb
  · intro c hc
    apply J.uliftYonedaEquiv.injective
    rw [Equiv.apply_symm_apply]
    apply huniq
    rw [J.uliftYonedaEquiv_naturality, hc]

/-- The Frobenius map coequalizes translation by its scheme-theoretic
kernel, including on nonreduced test schemes. -/
theorem kernelTranslation_coequalizes
    (F : A ⟶ AF) [IsMonHom F] :
    ((fst (Picard.Homomorphisms.Kernel.Construction.kernelScheme F) A ≫ Picard.Homomorphisms.Kernel.Construction.kernelInclusion F) *
        snd (Picard.Homomorphisms.Kernel.Construction.kernelScheme F) A) ≫ F =
      snd (Picard.Homomorphisms.Kernel.Construction.kernelScheme F) A ≫ F := by
  have hkernel : Picard.Homomorphisms.Kernel.Construction.kernelInclusion F ≫ F = 1 := by
    change equalizer.ι F 1 ≫ F = 1
    rw [equalizer.condition, MonObj.comp_one]
  rw [MonObj.mul_comp, Category.assoc, hkernel, MonObj.comp_one, one_mul]

/-- Homomorphisms identifies the independently constructed sheaf quotient by its
kernel with its actual target; this is the geometric quotient bridge. -/
def kernelQuotientIsoOfHomomorphisms
    (F : A ⟶ AF) [IsMonHom F]
    (h_Homomorphisms : Picard.Homomorphisms.Quotient.Construction.IsFppfQuotientByKernel F) :
    BaseChange.Construction.subgroupQuotient (Picard.Homomorphisms.Kernel.Construction.kernelInclusion F) ≅ (BaseChange.Construction.fppfPoints S).obj AF := by
  let H := Picard.Homomorphisms.Kernel.Construction.kernelScheme F
  let i := Picard.Homomorphisms.Kernel.Construction.kernelInclusion F
  let act := (fst H A ≫ i) * snd H A
  let p := (BaseChange.Construction.fppfPoints S).map F
  have hp : (BaseChange.Construction.fppfPoints S).map act ≫ p = (BaseChange.Construction.fppfPoints S).map (snd H A) ≫ p := by
    rw [← Functor.map_comp, ← Functor.map_comp, kernelTranslation_coequalizes]
  have hu (c : Cofork ((BaseChange.Construction.fppfPoints S).map act) ((BaseChange.Construction.fppfPoints S).map (snd H A))) :
      ∃! b : (BaseChange.Construction.fppfPoints S).obj AF ⟶ c.pt, p ≫ b = c.π :=
    kernelQuotient_desc_of_Homomorphisms F h_Homomorphisms c.pt c.π c.condition
  let hc : IsColimit (Cofork.ofπ p hp) :=
    Cofork.IsColimit.mk _ (fun c => Classical.choose (hu c))
      (fun c => (Classical.choose_spec (hu c)).1)
      (fun c b hb => (Classical.choose_spec (hu c)).2 b hb)
  exact (coequalizerIsCoequalizer ((BaseChange.Construction.fppfPoints S).map act)
    ((BaseChange.Construction.fppfPoints S).map (snd H A))).coconePointUniqueUpToIso hc

/-- The comparison identifies the quotient projection with Frobenius
itself. This pins down the induced marking and endomorphism transport. -/
theorem kernelQuotientIsoOfHomomorphisms_projection
    (F : A ⟶ AF) [IsMonHom F]
    (h_Homomorphisms : Picard.Homomorphisms.Quotient.Construction.IsFppfQuotientByKernel F) :
    BaseChange.Construction.relationQuotientProjection
        ((fst (Picard.Homomorphisms.Kernel.Construction.kernelScheme F) A ≫ Picard.Homomorphisms.Kernel.Construction.kernelInclusion F) *
          snd (Picard.Homomorphisms.Kernel.Construction.kernelScheme F) A)
        (snd (Picard.Homomorphisms.Kernel.Construction.kernelScheme F) A) ≫
      (kernelQuotientIsoOfHomomorphisms F h_Homomorphisms).hom = (BaseChange.Construction.fppfPoints S).map F := by
  dsimp only [kernelQuotientIsoOfHomomorphisms]
  apply IsColimit.comp_coconePointUniqueUpToIso_hom _ _ WalkingParallelPair.one
  apply Cofork.IsColimit.ofExistsUnique
  intro t
  exact kernelQuotient_desc_of_Homomorphisms F h_Homomorphisms t.pt t.π t.condition

end

end OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.Quotient.Construction
