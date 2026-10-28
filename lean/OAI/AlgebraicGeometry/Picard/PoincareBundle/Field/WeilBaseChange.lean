import OAI.AlgebraicGeometry.Picard.PoincareBundle.Field.WeilPairing
import OAI.AlgebraicGeometry.Picard.PoincareBundle.CharacterPointBaseChange
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Scalar.KernelPointBaseChange
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Isogeny.BaseChange

/-! # Weil Base Change -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.Field.WeilBaseChange

noncomputable section

/-! The actual Weil pairing of the original polarization commutes with field extension on every scheme-valued torsion pair. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

attribute [local instance] Homomorphisms.GroupDescent.Construction.groupHom_pow_isMonHom

variable {k K : Type} [Field k] [Field K] {a : ℕ} {A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme a (Spec (.of k))}
  (D : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData A) (ell : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.Isogeny A D.abelian) (n : ℕ) (hn : 0 < n)
  (s : Spec (.of K) ⟶ Spec (.of k))

/-- The full point equivalence preserves the n-torsion condition. -/
theorem torsion_original (T : Over (Spec (.of K))) (x : T ⟶ (A.pullback s).scheme) (hx : x ^ n = 1) :
    (A.baseChangePointsEquiv s T x) ^ n = 1 := by
  let e := A.baseChangePointsMulEquiv s T
  exact (map_pow e x n).symm.trans ((congrArg e hx).trans (map_one e))

/-- Base change of the supplied dual is the same actual normalized Poincare datum. -/
theorem dual_data : Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData.ofBundled (D.pullback s) = (Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData.ofBundled D).pullback s := rfl

/-- Character-line descent proves equality of the actual Weil units after field extension; no pairing compatibility is assumed. -/
theorem value (T : Over (Spec (.of K)))
    (x : T ⟶ (A.pullback s).scheme) (hx : x ^ n = 1)
    (y : T ⟶ (A.pullback s).scheme) (hy : y ^ n = 1) :
    WeilPairing.value (D.pullback s) (ell.pullback s) n hn x hx y hy =
      WeilPairing.value D ell n hn (A.baseChangePointsEquiv s T x) (torsion_original n s T x hx)
        (A.baseChangePointsEquiv s T y) (torsion_original n s T y hy) := by
  let D0 := Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData.ofBundled D
  let D1 := Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData.ofBundled (D.pullback s)
  let ell0 : A.scheme ⟶ D0.abelian := ell.hom
  let ell1 : (A.pullback s).scheme ⟶ D1.abelian := (ell.pullback s).hom
  have : IsMonHom ell0 := ell.preservesGroup
  have : IsFinite ell0.left := ell.finite
  have : Flat ell0.left := ell.flat
  have : Surjective ell0.left := ell.surjective
  have : IsMonHom ell1 := (ell.pullback s).preservesGroup
  have : IsFinite ell1.left := (ell.pullback s).finite
  have : Flat ell1.left := (ell.pullback s).flat
  have : Surjective ell1.left := (ell.pullback s).surjective
  have hc0 := Reference.Torsion.cover D ell n hn
  have : IsFinite ((𝟙 A.scheme) ^ n).left := hc0.1
  have : Flat ((𝟙 A.scheme) ^ n).left := hc0.2.1
  have : Surjective ((𝟙 A.scheme) ^ n).left := hc0.2.2.1
  have : LocallyOfFinitePresentation ((𝟙 A.scheme) ^ n).left := hc0.2.2.2.1
  have hc1 := Reference.Torsion.cover (D.pullback s) (ell.pullback s) n hn
  have : IsFinite ((𝟙 (A.pullback s).scheme) ^ n).left := hc1.1
  have : Flat ((𝟙 (A.pullback s).scheme) ^ n).left := hc1.2.1
  have : Surjective ((𝟙 (A.pullback s).scheme) ^ n).left := hc1.2.2.1
  have : LocallyOfFinitePresentation ((𝟙 (A.pullback s).scheme) ^ n).left := hc1.2.2.2.1
  let x0 := A.baseChangePointsEquiv s T x
  let y0 := A.baseChangePointsEquiv s T y
  have hx0 := torsion_original n s T x hx
  have hy0 := torsion_original n s T y hy
  have hpx0 := TorsionCharacterNaturality.image_torsion ell0 n x0 hx0
  have hpx := TorsionCharacterNaturality.image_torsion ell1 n x hx
  let C0 := Canonical.WeilData.representative D ell n hn
  let C1 := Canonical.WeilData.representative (D.pullback s) (ell.pullback s) n hn
  let χ := TorsionCharacterPoint.character A.scheme D0 ell0 n hn C0 (x0 ≫ ell0) hpx0
  let ψ := TorsionCharacterPoint.character (A.pullback s).scheme D1 ell1 n hn C1 (x ≫ ell1) hpx
  have hχ : AbelianScheme.CartierDuality.ParameterizedCharacterLines.Construction.KernelCharacters.parameterCharacterDualPoint ((𝟙 A.scheme) ^ n) ((Over.map s).obj T) χ D0 =
      Homomorphisms.UnbundledBaseChangePoints.Construction.UnbundledPicard.baseChangePointsEquiv D0.abelian s T (x ≫ ell1) :=
    (TorsionCharacterPoint.point A.scheme D0 ell0 n hn C0 (x0 ≫ ell0) hpx0).trans
      (AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.baseChangePointsEquiv_map ell.hom s T x).symm
  have hψ : AbelianScheme.CartierDuality.ParameterizedCharacterLines.Construction.KernelCharacters.parameterCharacterDualPoint ((𝟙 (A.pullback s).scheme) ^ n) T ψ (D0.pullback s) = x ≫ ell1 :=
    TorsionCharacterPoint.point (A.pullback s).scheme D1 ell1 n hn C1 (x ≫ ell1) hpx
  let g : (Over.pullback s).obj A.scheme ⟶ (Over.pullback s).obj A.scheme :=
    (𝟙 (A.pullback s).scheme) ^ n
  have hg : (Over.pullback s).map ((𝟙 A.scheme) ^ n) = g :=
    Scalar.KernelPointBaseChange.scalar_eq s A.scheme n
  have hm : IsMonHom ((Over.pullback s).map ((𝟙 A.scheme) ^ n)) := inferInstance
  have : IsMonHom g := hg ▸ hm
  have : IsFinite g.left := hc1.1
  have : Flat g.left := hc1.2.1
  have : Surjective g.left := hc1.2.2.1
  have : LocallyOfFinitePresentation g.left := hc1.2.2.2.1
  have hv := CharacterPointBaseChange.Congr.value_eq ((𝟙 A.scheme) ^ n) D0 s
    g hg
    T χ ψ (x ≫ ell1) hχ hψ (AbelianScheme.TorsionQuotient.SubgroupFunctor.torsionLift n y hy)
  have hz := Scalar.KernelPointBaseChange.lift_baseChange s A.scheme n T y hy hy0
  exact hv.trans (congrArg (fun z : (Over.map s).obj T ⟶ Homomorphisms.Kernel.Construction.kernelScheme ((𝟙 A.scheme) ^ n) =>
    AbelianScheme.CartierDuality.CharacterUnitValues.Construction.Schemes.multiplicativeGroupUnitHom ((Over.map s).obj T) (AbelianScheme.CartierDuality.Evaluation.Construction.CharacterEvaluation.value χ z)) hz)

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.Field.WeilBaseChange
