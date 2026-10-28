import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Intrinsic.KernelPoints
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Torsion.KernelParameter
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Intrinsic.MorphismKernel

/-! # Isotropy -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Intrinsic.Isotropy.Construction

noncomputable section

/-!
Self-annihilation holds for the actual kernel of the constructed native
isogeny, over its actual parameter scheme. The kernel is defined by the
original morphism and agrees with the scheme-theoretic kernel image.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

universe u

variable {S : Scheme.{u}} {d : ℕ} (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme d S) (P : Over S)
  (F : TorsionQuotient.SubgroupFunctor.RelativeSubgroup A.scheme P) (R : F.Model)
  {B : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme d P.left}
  (f : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.Isogeny (A.pullback P.hom) B)
  (hker : ∀ (U : Over P.left) (x : U ⟶ (A.pullback P.hom).scheme),
    x ≫ f.hom = 1 ↔ ∃! h : U ⟶ (Subgroup.Construction.subgroupGroupScheme F R).X,
      h ≫ Stability.Construction.nativeSubgroupInclusion A P F R = x)

include hker in
theorem nativeQuotient_kernel_eq_parameter :
    MorphismKernel.Construction.nativeMorphismKernel f.hom = Relative.ParameterBaseChange.Construction.relativeSubgroupOverParameter (Grp.mk A.scheme) P F := by
  ext U t x
  exact KernelPoints.Construction.nativeQuotient_kernel_membership A P F R f hker U x

include hker in
theorem nativeQuotient_kernel_self_annihilating (n : ℕ)
    (e : IsogenyQuotient.Annihilator.Construction.SchemeBicharacter (A := Torsion.Groups.Construction.nativeTorsionScheme A.scheme n) (B := Torsion.Groups.Construction.nativeTorsionScheme A.scheme n)
      (W := (CartierDuality.CharacterSheaf.Construction.Schemes.multiplicativeGroupOver S).X))
    (h : e.relativeAnnihilator (SubgroupTransport.Construction.relativeSubgroupPullback (Torsion.Groups.Construction.nativeTorsionInclusion A.scheme n) F) =
      SubgroupTransport.Construction.relativeSubgroupPullback (Torsion.Groups.Construction.nativeTorsionInclusion A.scheme n) F) :
    let H := SubgroupTransport.Construction.relativeSubgroupPullback (Torsion.Groups.Construction.nativeTorsionInclusion (A.pullback P.hom).scheme n)
      (MorphismKernel.Construction.nativeMorphismKernel f.hom)
    (TorsionPairingBaseChange.Construction.nativeTorsionPairingPullback P.hom (Grp.mk A.scheme) (Grp.mk A.scheme) n e).relativeAnnihilator H = H := by
  have hi := congrArg (SubgroupTransport.Construction.relativeSubgroupPullback (Torsion.Groups.Construction.nativeTorsionInclusion (A.pullback P.hom).scheme n))
    (nativeQuotient_kernel_eq_parameter A P F R f hker)
  exact (congrArg
    (TorsionPairingBaseChange.Construction.nativeTorsionPairingPullback P.hom (Grp.mk A.scheme) (Grp.mk A.scheme) n e).relativeAnnihilator hi).trans
      ((Torsion.KernelParameter.Construction.nativeTorsionSubgroupOverParameter_self_annihilating (Grp.mk A.scheme) P n F e h).trans hi.symm)

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Intrinsic.Isotropy.Construction
