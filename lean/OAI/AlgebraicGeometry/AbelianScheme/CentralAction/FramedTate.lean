import OAI.AlgebraicGeometry.AbelianScheme.CentralAction.SplitScalar
import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.Rational

/-! # Framed Tate -/

namespace OAI.AlgebraicGeometry.AbelianScheme.CentralAction.FramedTate.Construction

noncomputable section

/-! Actual Tate functoriality transports PEL equivariance to the split
coordinate maps used to recover a complete isogeny lattice. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.AbelianScheme.TateComparison.Rational

variable {S : Scheme} {A B C : Over S} [GrpObj A] [IsCommMonObj A]
  [GrpObj B] [IsCommMonObj B] [GrpObj C] [IsCommMonObj C]
  (T : Over S) (q : ℕ) [Fact q.Prime]

theorem schemeTateMap_comp (f : A ⟶ B) [IsMonHom f] (g : B ⟶ C) [IsMonHom g] :
    TateComparison.Add.schemeTateMap A T q (f ≫ g) = (TateComparison.Add.schemeTateMap B T q g).comp (TateComparison.Add.schemeTateMap A T q f) := by
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  funext n
  apply Subtype.ext
  change (x.val n).val.toMul ≫ (f ≫ g) = ((x.val n).val.toMul ≫ f) ≫ g
  exact (Category.assoc _ _ _).symm

theorem rationalTateMap_comp (f : A ⟶ B) [IsMonHom f] (g : B ⟶ C) [IsMonHom g] :
    TateComparison.Rational.rationalTateMap (T := T) (q := q) (f ≫ g) =
      (TateComparison.Rational.rationalTateMap (T := T) (q := q) g).comp (TateComparison.Rational.rationalTateMap (T := T) (q := q) f) := by
  rw [TateComparison.Rational.rationalTateMap, schemeTateMap_comp, LinearMap.baseChange_comp]
  rfl

theorem rationalTateMap_congr (f g : A ⟶ B) [IsMonHom f] [IsMonHom g] (hfg : f = g) :
    TateComparison.Rational.rationalTateMap (T := T) (q := q) f = TateComparison.Rational.rationalTateMap (T := T) (q := q) g := by
  subst g
  rfl

variable {R : Type} [CommRing R] {g N s n : ℕ}
  {P Q : TateComparison.PEL.PELFamilyData R g N S}

def framedRationalTateMap
    (e : TateComparison.Rational.SplitTateFrame s P.abelian.scheme T q)
    (e' : TateComparison.Rational.SplitTateFrame s Q.abelian.scheme T q) (f : TateComparison.PELIsogenies.PELIsogeny P Q n) :
    TateComparison.Rational.SplitTateSpace s q →ₗ[ℚ_[q]] TateComparison.Rational.SplitTateSpace s q :=
  e'.toLinearMap.comp ((TateComparison.Rational.rationalTateMap (T := T) (q := q) f.isogeny.hom).comp e.symm.toLinearMap)

/-- The diagonal intertwining equation is proved from the actual PEL
isogeny's action equation and the two supplied split Tate frames. -/
theorem framedRationalTateMap_intertwines
    (χ : Fin s × Bool → R →+* ℤ_[q])
    (e : TateComparison.Rational.SplitTateFrame s P.abelian.scheme T q)
    (e' : TateComparison.Rational.SplitTateFrame s Q.abelian.scheme T q)
    (he : TateComparison.Rational.IsSplitActionFrame P T q χ e) (he' : TateComparison.Rational.IsSplitActionFrame Q T q χ e')
    (f : TateComparison.PELIsogenies.PELIsogeny P Q n) (b : R) (x : TateComparison.Rational.SplitTateSpace s q) :
    framedRationalTateMap T q e e' f (fun v => (χ v b : ℚ_[q]) • x v) =
      fun v => (χ v b : ℚ_[q]) • framedRationalTateMap T q e e' f x v := by
  have hx : e.symm (fun v => (χ v b : ℚ_[q]) • x v) =
      TateComparison.Rational.rationalTateMap (T := T) (q := q) (TateComparison.End.endSchemeMap P.abelian.scheme (P.action b))
        (e.symm x) := by
    apply e.injective
    ext v i
    rw [e.apply_symm_apply, he]
    simp only [e.apply_symm_apply, Pi.smul_apply, smul_eq_mul]
  have hf := rationalTateMap_congr T q _ _ (f.equivariant b)
  rw [rationalTateMap_comp, rationalTateMap_comp] at hf
  have hh := LinearMap.congr_fun hf (e.symm x)
  simp only [LinearMap.comp_apply] at hh
  ext v i
  change e' (TateComparison.Rational.rationalTateMap (T := T) (q := q) f.isogeny.hom
      (e.symm (fun v => (χ v b : ℚ_[q]) • x v))) v i =
    (χ v b : ℚ_[q]) * e' (TateComparison.Rational.rationalTateMap (T := T) (q := q) f.isogeny.hom (e.symm x)) v i
  rw [hx, hh]
  exact he' b _ v i

end

end OAI.AlgebraicGeometry.AbelianScheme.CentralAction.FramedTate.Construction
