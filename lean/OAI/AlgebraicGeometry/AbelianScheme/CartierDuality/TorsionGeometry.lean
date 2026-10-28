import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.TorsionSheaves
import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.GeometricFiniteness
import OAI.AlgebraicGeometry.AbelianScheme.TorsionQuotient.Left
import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.MultiplicationFlat

/-! # Torsion Geometry -/

namespace OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.TorsionGeometry

noncomputable section

/-!
# CartierDuality: native and sheaf torsion geometry from finite multiplication
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

universe u

namespace Construction.Schemes

variable {S : Scheme.{u}} (G : Grp (Over S)) [IsCommMonObj G.X]
    [Smooth G.X.hom] [IsProper G.X.hom] [GeometricallyConnected G.X.hom]

/-- Finite multiplication on a smooth proper connected commutative
group gives a finite locally free actual torsion scheme in every characteristic. -/
theorem nativeTorsion_finiteLocallyFree_of_finite_power (n : ℕ)
    [IsFinite ((𝟙 G.X : G.X ⟶ G.X) ^ n).left] :
    IsFinite (TorsionQuotient.SubgroupFunctor.torsionScheme G.X n).hom ∧ Flat (TorsionQuotient.SubgroupFunctor.torsionScheme G.X n).hom ∧
      LocallyOfFinitePresentation (TorsionQuotient.SubgroupFunctor.torsionScheme G.X n).hom := by
  let sq := TorsionQuotient.Left.TorsionPullback.isPullback_left G.X n
  have hf : Flat ((𝟙 G.X : G.X ⟶ G.X) ^ n).left :=
    MultiplicationFlat.Construction.Multiplication.flat_power_of_isFinite G.X n
  have hp : LocallyOfFinitePresentation ((𝟙 G.X : G.X ⟶ G.X) ^ n).left :=
    MultiplicationFlat.Construction.Multiplication.locallyOfFinitePresentation_overEnd G.X _
  exact ⟨MorphismProperty.of_isPullback (P := @IsFinite) sq inferInstance,
    MorphismProperty.of_isPullback (P := @Flat) sq hf,
    MorphismProperty.of_isPullback (P := @LocallyOfFinitePresentation) sq hp⟩

/-- The actual commutative fppf sheaf torsion is finite locally free
whenever the native multiplication map is finite. -/
theorem torsionFppfAb_finiteLocallyFree_of_finite_power (n : ℕ)
    [IsFinite ((𝟙 G.X : G.X ⟶ G.X) ^ n).left] :
    SheafCharacterComparison.Construction.Schemes.FiniteLocallyFreeFppfAb S (TorsionSheaves.Construction.Schemes.torsionFppfAb (CommutativeSheavesAb.Construction.Schemes.representedFppfAb S G) n) := by
  obtain ⟨hf, hflat, hfp⟩ := nativeTorsion_finiteLocallyFree_of_finite_power G n
  exact @TorsionSheaves.Construction.Schemes.torsionFppfAb_finiteLocallyFree_of_native S G inferInstance n hf hflat hfp

/-- For the actual torsion sheaf over an arbitrary base, the remaining
geometric input is only finiteness at residue-characteristic primes. -/
theorem torsionFppfAb_finiteLocallyFree_of_geometric_characteristic_primes
    (hchar : ∀ (K : Type u) [Field K] [IsAlgClosed K] (a : Spec (.of K) ⟶ S)
      (p : ℕ), p.Prime → (p : K) = 0 →
      let B := (Over.pullback a).obj G.X
      letI : GrpObj B := Functor.grpObjObj
      IsFinite ((𝟙 B : B ⟶ B) ^ p).left)
    (n : ℕ) (hn : 0 < n) : SheafCharacterComparison.Construction.Schemes.FiniteLocallyFreeFppfAb S (TorsionSheaves.Construction.Schemes.torsionFppfAb (CommutativeSheavesAb.Construction.Schemes.representedFppfAb S G) n) := by
  let : IsFinite ((𝟙 G.X : G.X ⟶ G.X) ^ n).left :=
    GeometricFiniteness.Construction.Schemes.finite_positive_powers_of_geometric_characteristic_primes G.X hchar n hn
  exact torsionFppfAb_finiteLocallyFree_of_finite_power G n

end Construction.Schemes

end

end OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.TorsionGeometry
