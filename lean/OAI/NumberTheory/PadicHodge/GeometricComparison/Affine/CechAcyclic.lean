import OAI.NumberTheory.PadicHodge.GeometricComparison.OpenForms
import OAI.NumberTheory.PadicHodge.GeometricComparison.Intrinsic.AffineFormsCechVanishing
import OAI.NumberTheory.PadicHodge.GeometricComparison.Module.InjectiveFlasque
import OAI.NumberTheory.PadicHodge.GeometricComparison.Module.FlasqueCech

/-! # Cech Acyclic -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.Affine.CechAcyclic.AffineCechAcyclic

noncomputable section

/-! Native differential-form sheaves and injective sheaves satisfy positive principal Čech vanishing on every rational affine chart. -/

open _root_.CategoryTheory Limits _root_.AlgebraicGeometry

variable (R : Type) [CommRing R] (X : Over (Spec (CommRingCat.of R)))

def Acyclic (F : Sheaf (Opens.grothendieckTopology X.left) (ModuleCat R)) : Prop :=
  ∀ (A : Type) [CommRing A] [Algebra R A] [Algebra ℚ A]
    (f : RelativeSectionCoefficients.AffineCoordinates.relativeSpecModel R A ⟶ X) [IsOpenImmersion f.left]
    (t : Finset A), Ideal.span (t : Set A) = ⊤ → ∀ n : ℕ,
      ((Cech.CechSheaf.functor R (RelativeSectionCoefficients.AffineCoordinates.relativeSpecModel R A)
        (fun a : t => PrimeSpectrum.basicOpen a.val)).obj
          ((AlgebraicGeometry.Crystalline.Cohomology.Cech.Cover.CechRestriction.sheafRestrictionFunctor R f.left).obj F)).ExactAt (n + 1)

theorem of_iso {F G : Sheaf (Opens.grothendieckTopology X.left) (ModuleCat R)}
    (hF : Acyclic R X F) (e : F ≅ G) : Acyclic R X G := by
  intro A _ _ _ f _ t ht n
  exact (hF A f t ht n).of_iso
    ((Cech.CechSheaf.functor R (RelativeSectionCoefficients.AffineCoordinates.relativeSpecModel R A)
      (fun a : t => PrimeSpectrum.basicOpen a.val)).mapIso
        ((AlgebraicGeometry.Crystalline.Cohomology.Cech.Cover.CechRestriction.sheafRestrictionFunctor R f.left).mapIso e))

theorem injective (F : Sheaf (Opens.grothendieckTopology X.left) (ModuleCat R)) [Injective F] :
    Acyclic R X F := by
  intro A _ _ _ f _ t ht n
  have : TopCat.Sheaf.IsFlasque F := Module.InjectiveFlasque.ModuleInjectiveFlasque.flasque R X.left F
  have : TopCat.Sheaf.IsFlasque ((AlgebraicGeometry.Crystalline.Cohomology.Cech.Cover.CechRestriction.sheafRestrictionFunctor R f.left).obj F) :=
    Module.InjectiveFlasque.ModuleInjectiveFlasque.restriction R F f.left
  apply Module.FlasqueCech.ModuleFlasqueCech.exactAt_succ R (RelativeSectionCoefficients.AffineCoordinates.relativeSpecModel R A)
    ((AlgebraicGeometry.Crystalline.Cohomology.Cech.Cover.CechRestriction.sheafRestrictionFunctor R f.left).obj F)
    (fun a : t => PrimeSpectrum.basicOpen a.val) _ n
  apply PrimeSpectrum.iSup_basicOpen_eq_top_iff.mpr
  simpa only [Subtype.range_coe_subtype, Finset.setOfPred_mem] using ht

theorem forms (j : ℕ) : Acyclic R X
    ((presheafToSheaf (Opens.grothendieckTopology X.left) (ModuleCat R)).obj
      (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.formsPresheaf R X j)) := by
  intro A _ _ _ f _ t ht n
  have hs : Ideal.span (Set.range (fun a : t => a.val)) = ⊤ := by
    simpa only [Subtype.range_coe_subtype, Finset.setOfPred_mem] using ht
  exact (Intrinsic.AffineFormsCechVanishing.AffineCoordinates.nativeForms_cech_exactAt_succ R A (fun a : t => a.val) hs j n).of_iso
    ((Cech.CechSheaf.functor R (RelativeSectionCoefficients.AffineCoordinates.relativeSpecModel R A)
      (fun a : t => PrimeSpectrum.basicOpen a.val)).mapIso (OpenForms.OpenFormsSheaves.sheafIso f j).symm)

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.Affine.CechAcyclic.AffineCechAcyclic
