import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.KernelCharacterBaseChange
import OAI.AlgebraicGeometry.Picard.PoincareBundle.MonoidalScalarPreservation
import OAI.AlgebraicGeometry.Picard.Homomorphisms.UnbundledBaseChangePoints
import OAI.AlgebraicGeometry.AbelianScheme.TorsionQuotient.SubgroupFunctor

/-! # Kernel Point Base Change -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.Scalar.KernelPointBaseChange

noncomputable section

/-! Torsion points and the actual scalar-kernel base-change comparison have the same underlying scheme point. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

universe u

open OAI.AlgebraicGeometry.Picard.Homomorphisms.UnbundledBaseChangePoints.Construction.UnbundledPicard OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.KernelCharacterBaseChange.Construction.KernelCharacters

attribute [local instance] Homomorphisms.GroupDescent.Construction.groupHom_pow_isMonHom

/-- Equality of maps transports kernel objects without changing their inclusion. -/
theorem cast_inclusion {S : Scheme.{u}} {A B : Over S} [GrpObj B]
    (f g : A ⟶ B) (h : f = g) :
    eqToHom (congrArg (fun q : A ⟶ B => Homomorphisms.Kernel.Construction.kernelScheme q) h) ≫ Homomorphisms.Kernel.Construction.kernelInclusion g = Homomorphisms.Kernel.Construction.kernelInclusion f := by
  cases h
  simp only [eqToHom_refl, Category.id_comp]

variable {S S' : Scheme.{u}} (s : S' ⟶ S) (A : Over S) [GrpObj A] [IsCommMonObj A] (n : ℕ)

omit [IsCommMonObj A] in
/-- Scalar multiplication commutes with the actual pullback functor. -/
theorem scalar_eq : (Over.pullback s).map ((𝟙 A) ^ n) = (𝟙 ((Over.pullback s).obj A)) ^ n :=
  MonoidalScalarPreservation.map_scalar (Over.pullback s) A n

/-- The native kernel comparison sends the pulled torsion lift to the original torsion lift. -/
theorem lift_baseChange (T : Over S') (x : T ⟶ (Over.pullback s).obj A) (hx : x ^ n = 1)
    (hx0 : (Homomorphisms.UnbundledBaseChangePoints.Construction.UnbundledPicard.baseChangePointsEquiv A s T x) ^ n = 1) :
    AbelianScheme.CartierDuality.KernelCharacterBaseChange.Construction.KernelCharacters.baseChangeKernelPoint s ((𝟙 A) ^ n) T (AbelianScheme.TorsionQuotient.SubgroupFunctor.torsionLift n x hx ≫
      eqToHom (congrArg (fun q : (Over.pullback s).obj A ⟶ (Over.pullback s).obj A => Homomorphisms.Kernel.Construction.kernelScheme q)
        (scalar_eq s A n).symm)) = AbelianScheme.TorsionQuotient.SubgroupFunctor.torsionLift n (Homomorphisms.UnbundledBaseChangePoints.Construction.UnbundledPicard.baseChangePointsEquiv A s T x) hx0 := by
  let z := AbelianScheme.TorsionQuotient.SubgroupFunctor.torsionLift n x hx ≫
    eqToHom (congrArg (fun q : (Over.pullback s).obj A ⟶ (Over.pullback s).obj A => Homomorphisms.Kernel.Construction.kernelScheme q)
      (scalar_eq s A n).symm)
  have hz : z ≫ Homomorphisms.Kernel.Construction.kernelInclusion ((Over.pullback s).map ((𝟙 A) ^ n)) = x :=
    (Category.assoc _ _ _).trans
      ((congrArg (fun q => AbelianScheme.TorsionQuotient.SubgroupFunctor.torsionLift n x hx ≫ q)
        (cast_inclusion ((𝟙 ((Over.pullback s).obj A)) ^ n) ((Over.pullback s).map ((𝟙 A) ^ n))
          (scalar_eq s A n).symm)).trans (AbelianScheme.TorsionQuotient.SubgroupFunctor.torsionLift_ι n x hx))
  apply (cancel_mono (Homomorphisms.Kernel.Construction.kernelInclusion ((𝟙 A) ^ n))).mp
  have he := AbelianScheme.CartierDuality.KernelCharacterBaseChange.Construction.KernelCharacters.baseChangeKernelPoint_inclusion s ((𝟙 A) ^ n) T z
  exact he.trans ((congrArg (AbelianScheme.CartierDuality.CharacterBaseChange.Construction.Schemes.pullbackPointMulEquiv s (Grp.mk A) T).symm hz).trans
    (AbelianScheme.TorsionQuotient.SubgroupFunctor.torsionLift_ι n (Homomorphisms.UnbundledBaseChangePoints.Construction.UnbundledPicard.baseChangePointsEquiv A s T x) hx0).symm)

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.Scalar.KernelPointBaseChange
