import OAI.AlgebraicGeometry.HilbertScheme.Presentations.ModuleCech.Card
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Localized.FreeDegrees
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Polynomial.CechExactness

/-! # Free Module Cech Exactness -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.FreeModuleCechExactness.ProjectiveCech

noncomputable section

/-! High-degree exactness of the Čech complex of an actual weighted free module. -/

open _root_.MvPolynomial

universe u v w

variable {σ : Type u} [Fintype σ] [LinearOrder σ] [Nonempty σ]
variable (R : Type v) [CommRing R] (ι : Type w) [Fintype ι]

def freeCechAssemble (g : ι → Polynomial.Cech.ProjectiveCech.PolynomialCechFamily (σ := σ) R) :
    ModuleCech.Card.ProjectiveCech.ModuleCechFamily (σ := σ) R (ι →₀ MvPolynomial σ R) :=
  fun s => (Localized.FreeCoordinates.ProjectiveCech.freeLocalizedEquiv R ι s).symm
    (Finsupp.equivFunOnFinite.symm (fun i => g i s))

omit [Nonempty σ] [Fintype σ] [LinearOrder σ] in
theorem freeCechCoordinate_assemble (g : ι → Polynomial.Cech.ProjectiveCech.PolynomialCechFamily (σ := σ) R) (i : ι) :
    ModuleCech.Card.ProjectiveCech.freeCechCoordinate R ι i (freeCechAssemble R ι g) = g i := by
  funext s
  change Localized.FreeCoordinates.ProjectiveCech.freeLocalizedEquiv R ι s ((Localized.FreeCoordinates.ProjectiveCech.freeLocalizedEquiv R ι s).symm
    (Finsupp.equivFunOnFinite.symm (fun i => g i s))) i = _
  rw [LinearEquiv.apply_symm_apply]
  rfl

omit [Nonempty σ] [Fintype σ] [LinearOrder σ] [Fintype ι] in
theorem freeCechCoordinate_ext
    (f g : ModuleCech.Card.ProjectiveCech.ModuleCechFamily (σ := σ) R (ι →₀ MvPolynomial σ R))
    (h : ∀ i, ModuleCech.Card.ProjectiveCech.freeCechCoordinate R ι i f = ModuleCech.Card.ProjectiveCech.freeCechCoordinate R ι i g) : f = g := by
  funext s
  apply (Localized.FreeCoordinates.ProjectiveCech.freeLocalizedEquiv R ι s).injective
  ext i
  exact congrFun (h i) s

omit [Nonempty σ] [Fintype σ] [LinearOrder σ] [Fintype ι] in
theorem freeCechCoordinate_zero (i : ι) :
    ModuleCech.Card.ProjectiveCech.freeCechCoordinate (σ := σ) R ι i 0 = 0 := by
  funext s
  simp only [ModuleCech.Card.ProjectiveCech.freeCechCoordinate, Pi.zero_apply, map_zero, Finsupp.zero_apply]

omit [Nonempty σ] [Fintype σ] [LinearOrder σ] in
theorem freeCechAssemble_card (q : ℕ) (g : ι → Polynomial.Cech.ProjectiveCech.PolynomialCechFamily (σ := σ) R)
    (hg : ∀ i, Polynomial.Cech.ProjectiveCech.CechCardSupported R q (g i)) :
    ModuleCech.Card.ProjectiveCech.ModuleCechCardSupported R (ι →₀ MvPolynomial σ R) q (freeCechAssemble R ι g) := by
  intro s hs
  apply (Localized.FreeCoordinates.ProjectiveCech.freeLocalizedEquiv R ι s).injective
  ext i
  have he := congrFun (freeCechCoordinate_assemble R ι g i) s
  change Localized.FreeCoordinates.ProjectiveCech.freeLocalizedEquiv R ι s (freeCechAssemble R ι g s) i = g i s at he
  change Localized.FreeCoordinates.ProjectiveCech.freeLocalizedEquiv R ι s (freeCechAssemble R ι g s) i = Localized.FreeCoordinates.ProjectiveCech.freeLocalizedEquiv R ι s 0 i
  rw [map_zero, Finsupp.zero_apply, he]
  exact hg i s hs

omit [Nonempty σ] in
theorem freeCechAssemble_homogeneous (w : ι → ℤ) (d : ℤ)
    (g : ι → Polynomial.Cech.ProjectiveCech.PolynomialCechFamily (σ := σ) R) (hg : ∀ i, Polynomial.Cech.ProjectiveCech.CechHomogeneous R (d - w i) (g i)) :
    ModuleCech.Card.ProjectiveCech.ModuleCechHomogeneous R (ι →₀ MvPolynomial σ R) (WeightedFreeModules.GradedModules.weightedFreeGrading R w) d
      (freeCechAssemble R ι g) := by
  intro s
  rw [Localized.FreeDegrees.ProjectiveCech.freeLocalizedEquiv_degree_iff]
  intro i
  have he := congrFun (freeCechCoordinate_assemble R ι g i) s
  change Localized.FreeCoordinates.ProjectiveCech.freeLocalizedEquiv R ι s (freeCechAssemble R ι g s) i = g i s at he
  change Localized.FreeCoordinates.ProjectiveCech.freeLocalizedEquiv R ι s (freeCechAssemble R ι g s) i ∈ _
  rw [he]
  exact hg i s

theorem freeModuleCech_exact (w : ι → ℤ) (d : ℤ) (hd : ∀ i, w i ≤ d) (q : ℕ)
    (f : ModuleCech.Card.ProjectiveCech.ModuleCechFamily (σ := σ) R (ι →₀ MvPolynomial σ R))
    (hf : ModuleCech.Card.ProjectiveCech.ModuleCechHomogeneous R (ι →₀ MvPolynomial σ R) (WeightedFreeModules.GradedModules.weightedFreeGrading R w) d f)
    (hcard : ModuleCech.Card.ProjectiveCech.ModuleCechCardSupported R (ι →₀ MvPolynomial σ R) (q + 1) f)
    (hcocycle : ModuleCech.Card.ProjectiveCech.moduleCechDifferential R (ι →₀ MvPolynomial σ R) f = 0) :
    ∃ g : ModuleCech.Card.ProjectiveCech.ModuleCechFamily (σ := σ) R (ι →₀ MvPolynomial σ R),
      ModuleCech.Card.ProjectiveCech.ModuleCechHomogeneous R (ι →₀ MvPolynomial σ R) (WeightedFreeModules.GradedModules.weightedFreeGrading R w) d g ∧
      ModuleCech.Card.ProjectiveCech.ModuleCechCardSupported R (ι →₀ MvPolynomial σ R) q g ∧
      ModuleCech.Card.ProjectiveCech.moduleCechDifferential R (ι →₀ MvPolynomial σ R) g = f := by
  have hcoord (i : ι) : Polynomial.Cech.ProjectiveCech.CechHomogeneous R (d - w i) (ModuleCech.Card.ProjectiveCech.freeCechCoordinate R ι i f) :=
    fun s => Localized.FreeDegrees.ProjectiveCech.freeLocalizedEquiv_degree R w s d (f s) (hf s) i
  have hcoordcard (i : ι) : Polynomial.Cech.ProjectiveCech.CechCardSupported R (q + 1) (ModuleCech.Card.ProjectiveCech.freeCechCoordinate R ι i f) := by
    intro s hs
    change Localized.FreeCoordinates.ProjectiveCech.freeLocalizedEquiv R ι s (f s) i = 0
    rw [hcard s hs, map_zero, Finsupp.zero_apply]
  have hcoordcycle (i : ι) : Polynomial.Cech.ProjectiveCech.polynomialCechDifferential R (ModuleCech.Card.ProjectiveCech.freeCechCoordinate R ι i f) = 0 := by
    rw [← ModuleCech.Card.ProjectiveCech.freeCechCoordinate_differential, hcocycle, freeCechCoordinate_zero]
  choose g hg hgcard hgd using fun i => Polynomial.CechExactness.ProjectiveCech.polynomialCech_exact R (d - w i)
    (sub_nonneg.mpr (hd i)) q (ModuleCech.Card.ProjectiveCech.freeCechCoordinate R ι i f) (hcoord i) (hcoordcard i) (hcoordcycle i)
  refine ⟨freeCechAssemble R ι g, freeCechAssemble_homogeneous R ι w d g hg,
    freeCechAssemble_card R ι q g hgcard, ?_⟩
  apply freeCechCoordinate_ext R ι
  intro i
  rw [ModuleCech.Card.ProjectiveCech.freeCechCoordinate_differential, freeCechCoordinate_assemble]
  exact hgd i

omit [Fintype ι] in
theorem freeModuleCech_augmentation_injective (w : ι → ℤ) (d : ℤ) (hd : ∀ i, w i ≤ d)
    (f : ModuleCech.Card.ProjectiveCech.ModuleCechFamily (σ := σ) R (ι →₀ MvPolynomial σ R))
    (hf : ModuleCech.Card.ProjectiveCech.ModuleCechHomogeneous R (ι →₀ MvPolynomial σ R) (WeightedFreeModules.GradedModules.weightedFreeGrading R w) d f)
    (hcard : ModuleCech.Card.ProjectiveCech.ModuleCechCardSupported R (ι →₀ MvPolynomial σ R) 0 f)
    (hcocycle : ModuleCech.Card.ProjectiveCech.moduleCechDifferential R (ι →₀ MvPolynomial σ R) f = 0) : f = 0 := by
  apply freeCechCoordinate_ext R ι
  intro i
  rw [freeCechCoordinate_zero]
  apply Polynomial.CechExactness.ProjectiveCech.polynomialCech_augmentation_injective R (d - w i) (sub_nonneg.mpr (hd i))
  · exact fun s => Localized.FreeDegrees.ProjectiveCech.freeLocalizedEquiv_degree R w s d (f s) (hf s) i
  · intro s hs
    change Localized.FreeCoordinates.ProjectiveCech.freeLocalizedEquiv R ι s (f s) i = 0
    rw [hcard s hs, map_zero, Finsupp.zero_apply]
  · rw [← ModuleCech.Card.ProjectiveCech.freeCechCoordinate_differential, hcocycle, freeCechCoordinate_zero]

def freeCechDegreeBound (w : ι → ℤ) : ℕ := ∑ i, (w i).toNat

omit [Fintype σ] [LinearOrder σ] [Nonempty σ] in
theorem freeCechDegreeBound_ge (w : ι → ℤ) (i : ι) : w i ≤ (freeCechDegreeBound ι w : ℤ) := by
  have hi : (w i).toNat ≤ freeCechDegreeBound ι w :=
    Finset.single_le_sum (f := fun i => (w i).toNat) (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
  have hi' : ((w i).toNat : ℤ) ≤ (freeCechDegreeBound ι w : ℤ) := by exact_mod_cast hi
  omega

theorem freeModuleCech_eventually_exact (w : ι → ℤ) (d : ℤ)
    (hd : (freeCechDegreeBound ι w : ℤ) ≤ d) (q : ℕ)
    (f : ModuleCech.Card.ProjectiveCech.ModuleCechFamily (σ := σ) R (ι →₀ MvPolynomial σ R))
    (hf : ModuleCech.Card.ProjectiveCech.ModuleCechHomogeneous R (ι →₀ MvPolynomial σ R) (WeightedFreeModules.GradedModules.weightedFreeGrading R w) d f)
    (hcard : ModuleCech.Card.ProjectiveCech.ModuleCechCardSupported R (ι →₀ MvPolynomial σ R) (q + 1) f)
    (hcocycle : ModuleCech.Card.ProjectiveCech.moduleCechDifferential R (ι →₀ MvPolynomial σ R) f = 0) :
    ∃ g : ModuleCech.Card.ProjectiveCech.ModuleCechFamily (σ := σ) R (ι →₀ MvPolynomial σ R),
      ModuleCech.Card.ProjectiveCech.ModuleCechHomogeneous R (ι →₀ MvPolynomial σ R) (WeightedFreeModules.GradedModules.weightedFreeGrading R w) d g ∧
      ModuleCech.Card.ProjectiveCech.ModuleCechCardSupported R (ι →₀ MvPolynomial σ R) q g ∧
      ModuleCech.Card.ProjectiveCech.moduleCechDifferential R (ι →₀ MvPolynomial σ R) g = f :=
  freeModuleCech_exact R ι w d (fun i => (freeCechDegreeBound_ge ι w i).trans hd) q f hf hcard hcocycle

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.FreeModuleCechExactness.ProjectiveCech
