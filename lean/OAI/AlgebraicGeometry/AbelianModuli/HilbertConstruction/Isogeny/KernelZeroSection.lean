import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Isogeny.KernelScheme
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.UnramifiedSections

/-! # Kernel Zero Section -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! The zero section of the actual isogeny kernel is an open immersion when that kernel is unramified. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.CategoryTheory.MonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj
universe u

variable {S : Scheme.{u}} {g h : ℕ} {A : Abelian.Schemes.AbelianScheme g S} {B : Abelian.Schemes.AbelianScheme h S}
variable (p : Abelian.Schemes.AbelianScheme.Isogeny A B)

def Abelian.Schemes.AbelianScheme.Isogeny.kernelZeroSection : 𝟙_ (Over S) ⟶ p.kernelScheme :=
  (p.kernelSchemePointsEquiv _).symm ⟨1, map_one (A.mapPoints B p.hom _)⟩

@[reassoc (attr := simp)] theorem Abelian.Schemes.AbelianScheme.Isogeny.kernelZeroSection_inclusion : p.kernelZeroSection ≫ p.kernelInclusion = 1 :=
  congrArg (fun x : p.kernelAt (𝟙_ (Over S)) => x.val)
    ((p.kernelSchemePointsEquiv _).apply_symm_apply ⟨1, map_one (A.mapPoints B p.hom _)⟩)

theorem Abelian.Schemes.AbelianScheme.Isogeny.kernelZeroSection_isOpenImmersion [FormallyUnramified p.kernelScheme.hom] :
    IsOpenImmersion p.kernelZeroSection.left :=
  UnramifiedSections.section_isOpenImmersion_of_unramified p.kernelScheme.hom p.kernelZeroSection.left p.kernelZeroSection.w

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
