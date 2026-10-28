import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.Polarization
import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.FlagComposites

/-! # Polarized Composites -/

namespace OAI.AlgebraicGeometry.AbelianScheme.TateComparison

noncomputable section

/-! Actual polarized isogeny and flag composition equations are carried
to the integral Tate modules, including the dual map and multiplier. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

universe u
variable {S : Scheme.{u}} {A B : Over S} [GrpObj A] [IsCommMonObj A]
  [GrpObj B] [IsCommMonObj B] (T : Over S) (q : ℕ) [Fact q.Prime]

instance PolarizedComposites.isMonHom_pointwisePow (f : A ⟶ B) [IsMonHom f] (n : ℕ) : IsMonHom (f ^ n) := by
  induction n with
  | zero =>
    rw [pow_zero, CategoryTheory.Hom.one_def]
    infer_instance
  | succ n ih =>
    let : IsMonHom (f ^ n) := ih
    rw [pow_succ, CategoryTheory.Hom.mul_def]
    infer_instance

theorem PolarizedComposites.schemeTateMap_congr (f g : A ⟶ B) [IsMonHom f] [IsMonHom g] (w : f = g) :
    Add.schemeTateMap A T q f = Add.schemeTateMap A T q g := by
  subst g
  rfl

theorem PolarizedComposites.schemeTateMap_pow (f : A ⟶ B) [IsMonHom f] (n : ℕ) :
    Add.schemeTateMap A T q (f ^ n) = n • Add.schemeTateMap A T q f := by
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  funext k
  apply Subtype.ext
  exact congrArg Additive.ofMul (MonObj.comp_pow f n (x.val k).val.toMul)

variable {R : Type u} [CommRing R] {g N n : ℕ} {P Q : PEL.PELFamilyData R g N S}

theorem PELIsogenies.PELIsogeny.tate_polarization (e : PELIsogenies.PELIsogeny P Q n) :
    (Add.schemeTateMap Q.dual.abelian.scheme T q e.dualHom).comp
      ((Add.schemeTateMap Q.abelian.scheme T q Q.polarizationMap.hom).comp
        (Add.schemeTateMap P.abelian.scheme T q e.isogeny.hom)) =
      n • Add.schemeTateMap P.abelian.scheme T q P.polarizationMap.hom := by
  rw [← Functor.schemeTateMap_comp, ← Functor.schemeTateMap_comp]
  exact (PolarizedComposites.schemeTateMap_congr T q _ _
    ((Category.assoc _ _ _).trans e.polarization)).trans
      (PolarizedComposites.schemeTateMap_pow T q P.polarizationMap.hom n)

end

end OAI.AlgebraicGeometry.AbelianScheme.TateComparison
