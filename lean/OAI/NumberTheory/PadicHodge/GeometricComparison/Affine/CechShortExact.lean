import OAI.NumberTheory.PadicHodge.GeometricComparison.Affine.CechSectionEpi
import OAI.AlgebraicGeometry.Crystalline.Cohomology.Finite.PrincipalIntersections
import OAI.AlgebraicGeometry.Crystalline.Cohomology.Module.ProductSurjectivity
import Mathlib.Algebra.Homology.HomologicalComplexAbelian

/-! # Cech Short Exact -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.Affine.CechShortExact.AffineCechAcyclic

noncomputable section

/-! An affine Čech-acyclic kernel makes the actual principal Čech sequence of a short exact sheaf sequence degreewise short exact. -/

open _root_.CategoryTheory Limits _root_.AlgebraicGeometry Opposite Simplicial

variable (R : Type) [CommRing R] (X : Over (Spec (CommRingCat.of R)))
  (S : ShortComplex (Sheaf (Opens.grothendieckTopology X.left) (ModuleCat R)))
  (A : Type) [CommRing A] [Algebra R A] [Algebra ℚ A]
  (f : RelativeSectionCoefficients.AffineCoordinates.relativeSpecModel R A ⟶ X) [IsOpenImmersion f.left]
  {ι : Type} (s : ι → A)

local notation "U" => fun i => OAI.AlgebraicGeometry.Crystalline.Cohomology.Affine.IntersectionLocalization.AffineIntersectionLocalization.principal A (s i)
local notation "N" => FormalCoproduct.cech (FormalCoproduct.mk ι U)

def chartFunctor : Sheaf (Opens.grothendieckTopology X.left) (ModuleCat R) ⥤
    CochainComplex (ModuleCat R) ℕ :=
  AlgebraicGeometry.Crystalline.Cohomology.Cech.Cover.CechRestriction.sheafRestrictionFunctor R f.left ⋙
    Cech.CechSheaf.functor R (RelativeSectionCoefficients.AffineCoordinates.relativeSpecModel R A) U

instance chartFunctor_additive : (chartFunctor R X A f s).Additive where
  map_add {F G} φ ψ := by
    let : (Cech.CechSheaf.functor R (RelativeSectionCoefficients.AffineCoordinates.relativeSpecModel R A) U).Additive :=
      Cech.CechSheaf.functor_additive R (RelativeSectionCoefficients.AffineCoordinates.relativeSpecModel R A) U
    exact (congrArg (Cech.CechSheaf.functor R (RelativeSectionCoefficients.AffineCoordinates.relativeSpecModel R A) U).map
      ((AlgebraicGeometry.Crystalline.Cohomology.Cech.Cover.CechRestriction.sheafRestrictionFunctor R f.left).map_add (f := φ) (g := ψ))).trans
        (Cech.CechSheaf.functor R (RelativeSectionCoefficients.AffineCoordinates.relativeSpecModel R A) U).map_add

theorem degree_epi (hS : S.ShortExact) (hA : CechAcyclic.AffineCechAcyclic.Acyclic R X S.X₁) (n : ℕ) :
    Epi (((Cech.CechSheaf.functor R (RelativeSectionCoefficients.AffineCoordinates.relativeSpecModel R A) U).map
      ((AlgebraicGeometry.Crystalline.Cohomology.Cech.Cover.CechRestriction.sheafRestrictionFunctor R f.left).map S.g)).f n) := by
  change Epi (Limits.Pi.map (fun t : ((N).obj (op ⦋n⦌)).I =>
    ((AlgebraicGeometry.Crystalline.Cohomology.Cech.Cover.CechRestriction.sheafRestrictionFunctor R f.left).map S.g).hom.app
      (op (((N).obj (op ⦋n⦌)).obj t))))
  apply AlgebraicGeometry.Crystalline.Cohomology.Module.ProductSurjectivity.ModuleProductSurjectivity.epi
  intro t
  have he : ((N).obj (op ⦋n⦌)).obj t = PrimeSpectrum.basicOpen (∏ i, s (t i)) :=
    AlgebraicGeometry.Crystalline.Cohomology.Finite.PrincipalIntersections.FinitePrincipalIntersections.categoricalProduct A (fun i => s (t i))
  exact he.symm ▸ CechSectionEpi.AffineCechAcyclic.principal_section_epi R X S hS hA A f (∏ i, s (t i))

theorem shortExact (hS : S.ShortExact) (hA : CechAcyclic.AffineCechAcyclic.Acyclic R X S.X₁) :
    (S.map (chartFunctor R X A f s)).ShortExact := by
  have := hS.mono_f
  have := hS.epi_g
  let T := S.map (AlgebraicGeometry.Crystalline.Cohomology.Cech.Cover.CechRestriction.sheafRestrictionFunctor R f.left)
  have hT : T.ShortExact := hS.map (AlgebraicGeometry.Crystalline.Cohomology.Cech.Cover.CechRestriction.sheafRestrictionFunctor R f.left)
  have := hT.mono_f
  apply HomologicalComplex.shortExact_of_degreewise_shortExact
  intro n
  exact {
    exact := Cech.CechSheaf.degree_exact R (RelativeSectionCoefficients.AffineCoordinates.relativeSpecModel R A) U T hT.exact n
    mono_f := Cech.CechSheaf.degree_mono R (RelativeSectionCoefficients.AffineCoordinates.relativeSpecModel R A) U T n
    epi_g := degree_epi R X S A f s hS hA n }

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.Affine.CechShortExact.AffineCechAcyclic
