import OAI.AlgebraicGeometry.Picard.PoincareBundle.Field.WeilPairing
import OAI.AlgebraicGeometry.Picard.PoincareBundle.WeilTorsionCharacter
import OAI.AlgebraicGeometry.Picard.PoincareBundle.WeilUnitDetection

/-! # Weil Canonical Comparison -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.Field.WeilCanonicalComparison

noncomputable section

/-! The original-field Cartier evaluation is exactly the standard canonical Weil pairing already used by the descent theorem. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

attribute [local instance] Homomorphisms.GroupDescent.Construction.groupHom_pow_isMonHom Kernel.Scheme.kernelGroup

/-- The represented scalar kernel retains its full n-torsion condition. -/
theorem kernel_torsion {S : Scheme} (A : Over S) [GrpObj A] [IsCommMonObj A] (n : ℕ)
    {T : Over S} (z : T ⟶ Kernel.Scheme.kernelObject ((𝟙 A) ^ n)) :
    (z ≫ Kernel.Scheme.kernelInclusion ((𝟙 A) ^ n)) ^ n = 1 := by
  have h := (Kernel.Scheme.kernelPointsEquiv ((𝟙 A) ^ n) T z).property
  change (z ≫ Kernel.Scheme.kernelInclusion ((𝟙 A) ^ n)) ≫ (𝟙 A) ^ n = 1 at h
  simpa only [MonObj.comp_pow, Category.comp_id] using h

/-- The equalizer and fiber-product torsion representations have identical included points. -/
theorem native_lift {S : Scheme} (A : Over S) [GrpObj A] [IsCommMonObj A] (n : ℕ)
    {T : Over S} (z : T ⟶ Kernel.Scheme.kernelObject ((𝟙 A) ^ n)) :
    AbelianScheme.TorsionQuotient.SubgroupFunctor.torsionLift n (z ≫ Kernel.Scheme.kernelInclusion ((𝟙 A) ^ n)) (kernel_torsion A n z) =
      z ≫ (Homomorphisms.KernelGroup.Construction.kernelSchemePullbackIso ((𝟙 A) ^ n)).inv := by
  apply (cancel_mono (Homomorphisms.Kernel.Construction.kernelInclusion ((𝟙 A) ^ n))).mp
  let e := Homomorphisms.KernelGroup.Construction.kernelSchemePullbackIso ((𝟙 A) ^ n)
  let i := Kernel.Scheme.kernelInclusion ((𝟙 A) ^ n)
  have hi : e.inv ≫ Homomorphisms.Kernel.Construction.kernelInclusion ((𝟙 A) ^ n) = i :=
    (congrArg (fun q => e.inv ≫ q) (Homomorphisms.KernelGroup.Construction.kernelSchemePullbackIso_inclusion ((𝟙 A) ^ n)).symm).trans
      ((Category.assoc e.inv e.hom i).symm.trans
        ((congrArg (fun q => q ≫ i) e.inv_hom_id).trans (Category.id_comp i)))
  have hr : (z ≫ e.inv) ≫ Homomorphisms.Kernel.Construction.kernelInclusion ((𝟙 A) ^ n) = z ≫ i :=
    (Category.assoc _ _ _).trans (congrArg (fun q => z ≫ q) hi)
  exact (AbelianScheme.TorsionQuotient.SubgroupFunctor.torsionLift_ι n _ _).trans hr.symm

variable {k : Type} [Field k] [IsAlgClosed k] {a : ℕ} {A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme a (Spec (.of k))}
  (D : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData A) (ell : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.Isogeny A D.abelian) (n : ℕ) (hn : 0 < n)

/-- The newly exposed original-field unit is the actual canonical standard Weil value on every test pair. -/
theorem unit_value {T : Over (Spec (.of k))}
    (x y : T ⟶ Kernel.Scheme.kernelObject ((𝟙 A.scheme) ^ n)) :
    WeilPairing.value D ell n hn
      (x ≫ Kernel.Scheme.kernelInclusion ((𝟙 A.scheme) ^ n)) (kernel_torsion A.scheme n x)
      (y ≫ Kernel.Scheme.kernelInclusion ((𝟙 A.scheme) ^ n)) (kernel_torsion A.scheme n y) =
        WeilUnitDetection.unitValue T (Canonical.WeilData.value D ell n hn x y) := by
  let D0 := Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData.ofBundled D
  let ell0 : A.scheme ⟶ D0.abelian := ell.hom
  have : IsMonHom ell0 := ell.preservesGroup
  have : IsFinite ell0.left := ell.finite
  have : Flat ell0.left := ell.flat
  have : Surjective ell0.left := ell.surjective
  have : IsMonHom (show A.scheme ⟶ D0.withPicardGroup.abelian from ell0) :=
    Compatibility.isMonHom D0 ell0
  have : IsFinite (show A.scheme ⟶ D0.withPicardGroup.abelian from ell0).left := ell.finite
  have : Flat (show A.scheme ⟶ D0.withPicardGroup.abelian from ell0).left := ell.flat
  have : Surjective (show A.scheme ⟶ D0.withPicardGroup.abelian from ell0).left := ell.surjective
  have hc := Reference.Torsion.cover D ell n hn
  have : IsFinite ((𝟙 A.scheme) ^ n).left := hc.1
  have : Flat ((𝟙 A.scheme) ^ n).left := hc.2.1
  have : Surjective ((𝟙 A.scheme) ^ n).left := hc.2.2.1
  have : LocallyOfFinitePresentation ((𝟙 A.scheme) ^ n).left := hc.2.2.2.1
  let C := Canonical.WeilData.representative D ell n hn
  let Q := Kernel.Scheme.kernelObject ((𝟙 A.scheme) ^ n)
  let i : Q ⟶ A.scheme := Kernel.Scheme.kernelInclusion ((𝟙 A.scheme) ^ n)
  have hi : i ^ n = 1 := by
    simpa only [Category.id_comp] using kernel_torsion A.scheme n (𝟙 Q)
  have hip := TorsionCharacterNaturality.image_torsion ell0 n i hi
  have hipc : (show Q ⟶ D0.withPicardGroup.abelian from i ≫ ell0) ^ n = 1 := by
    change (letI := Homomorphisms.UnbundledDualGroup.Construction.UnbundledPicard.dualPicardGroup D0; (i ≫ ell0) ^ n = 1)
    rw [Compatibility.group_eq D0]
    exact hip
  let χ := TorsionCharacterPoint.character A.scheme D0 ell0 n hn C (i ≫ ell0) hip
  let yN := y ≫ (Homomorphisms.KernelGroup.Construction.kernelSchemePullbackIso ((𝟙 A.scheme) ^ n)).inv
  have hw : Canonical.WeilData.value D ell n hn x y = ULift.up (χ.app (.op (Over.mk x)) yN) :=
    WeilTorsionCharacter.value A.scheme D0 ell0 n hn C (i ≫ ell0) hipc x yN
  have hpx := TorsionCharacterNaturality.image_torsion ell0 n (x ≫ i) (kernel_torsion A.scheme n x)
  have hχ : (AbelianScheme.CartierDuality.CharacterSheaf.Construction.Schemes.characterSheaf (Spec (.of k)) (Grp.mk (Homomorphisms.Kernel.Construction.kernelScheme ((𝟙 A.scheme) ^ n)))).obj.map x.op χ =
      TorsionCharacterPoint.character A.scheme D0 ell0 n hn C ((x ≫ i) ≫ ell0) hpx := by
    apply TorsionCharacterPoint.unique A.scheme D0 ell0 n hn C
    exact (AbelianScheme.CartierDuality.ParameterLineNaturality.Construction.KernelCharacters.parameterCharacterDualPoint_natural ((𝟙 A.scheme) ^ n) x χ D0).symm.trans
      ((congrArg (fun p => x ≫ p) (TorsionCharacterPoint.point A.scheme D0 ell0 n hn C (i ≫ ell0) hip)).trans
        (Category.assoc x i ell0).symm)
  have hyN := native_lift A.scheme n y
  have he := congrArg₂ (fun (ψ : (AbelianScheme.CartierDuality.CharacterSheaf.Construction.Schemes.characterSheaf (Spec (.of k)) (Grp.mk (Homomorphisms.Kernel.Construction.kernelScheme ((𝟙 A.scheme) ^ n)))).obj.obj (.op T))
      (z : T ⟶ Homomorphisms.Kernel.Construction.kernelScheme ((𝟙 A.scheme) ^ n)) => AbelianScheme.CartierDuality.Evaluation.Construction.CharacterEvaluation.value ψ z) hχ.symm hyN
  have hv := he.trans (AbelianScheme.CartierDuality.Evaluation.Construction.CharacterEvaluation.value_restrict x χ yN)
  exact (congrArg (AbelianScheme.CartierDuality.CharacterUnitValues.Construction.Schemes.multiplicativeGroupUnitHom T) hv).trans
    (congrArg (WeilUnitDetection.unitValue T) hw).symm

/-- Identity detection agrees with the original canonical standard pairing. -/
theorem eq_one_iff {T : Over (Spec (.of k))}
    (x y : T ⟶ Kernel.Scheme.kernelObject ((𝟙 A.scheme) ^ n)) :
    Canonical.WeilData.value D ell n hn x y = 1 ↔
      WeilPairing.value D ell n hn
        (x ≫ Kernel.Scheme.kernelInclusion ((𝟙 A.scheme) ^ n)) (kernel_torsion A.scheme n x)
        (y ≫ Kernel.Scheme.kernelInclusion ((𝟙 A.scheme) ^ n)) (kernel_torsion A.scheme n y) = 1 :=
  (WeilUnitDetection.eq_one_iff T _).trans ((congrArg (fun z => z = 1) (unit_value D ell n hn x y).symm).to_iff)

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.Field.WeilCanonicalComparison
