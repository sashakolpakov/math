import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Geometric.PairedTorsionKernels
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Geometric.PairingCharacters
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Finite.EtaleKernelModels

/-! # Paired Kernel Type -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Geometric.PairedKernelType

noncomputable section

/-! Complementary geometric isogeny kernels have the same finite
group type. The comparison uses the original torsion image, canonical
pairing, and native inclusion into the full isogeny kernel. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

def nativeTorsionKernelPointEquiv
    {S : Scheme.{0}} {A B : Over S} [GrpObj A] [GrpObj B]
    [IsCommMonObj A] [IsCommMonObj B] (q : A ⟶ B) [IsMonHom q]
    (n : ℕ) (T : Over S)
    (hk : ∀ x : T ⟶ A, x ≫ q = 1 → x ^ n = 1) :
    (IsMonHom.monoidHom (AbelianScheme.IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionMap n q) T).ker ≃*
      (IsMonHom.monoidHom q T).ker := by
  let f : (IsMonHom.monoidHom (AbelianScheme.IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionMap n q) T).ker →*
      (IsMonHom.monoidHom q T).ker := {
    toFun x := ⟨x.val ≫ AbelianScheme.IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionInclusion A n,
      (Paired.PELKernelAnnihilator.nativeTorsionMap_kernel_point_iff q n T x.val).mp x.property⟩
    map_one' := Subtype.ext (MonObj.one_comp (AbelianScheme.IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionInclusion A n))
    map_mul' x y := Subtype.ext (MonObj.mul_comp x.val y.val (AbelianScheme.IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionInclusion A n)) }
  apply MulEquiv.ofBijective f
  constructor
  · intro x y h
    apply Subtype.ext
    apply (cancel_mono (AbelianScheme.IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionInclusion A n)).mp
    exact congrArg Subtype.val h
  · intro y
    let z := AbelianScheme.IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionLift A n y.val (hk y.val y.property)
    have hz : z ≫ AbelianScheme.IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionMap n q = 1 := by
      apply (Paired.PELKernelAnnihilator.nativeTorsionMap_kernel_point_iff q n T z).mpr
      rw [AbelianScheme.IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionLift_inclusion]
      exact y.property
    exact ⟨⟨z, hz⟩, Subtype.ext (AbelianScheme.IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionLift_inclusion A n y.val (hk y.val y.property))⟩

theorem geometric_paired_native_kernel_type
    {k : Type} [Field k] [CharZero k] [IsAlgClosed k]
    {A B : Over (Spec (.of k))} [GrpObj A] [GrpObj B]
    [IsCommMonObj A] [IsCommMonObj B]
    (q : A ⟶ B) [IsMonHom q] [Surjective q.left] [LocallyOfFiniteType q.left]
    (v : B ⟶ A) [IsMonHom v] (n : ℕ) (hqv : q ≫ v = (𝟙 A) ^ n)
    (hvq : v ≫ q = (𝟙 B) ^ n)
    [IsFinite (AbelianScheme.IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionScheme A n).hom] [Etale (AbelianScheme.IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionScheme A n).hom]
    [IsFinite (AbelianScheme.IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionScheme B n).hom] [Etale (AbelianScheme.IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionScheme B n).hom]
    (e : AbelianScheme.IsogenyQuotient.Annihilator.Construction.SchemeBicharacter (A := AbelianScheme.IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionScheme A n)
      (B := AbelianScheme.IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionScheme A n) (W := (AbelianScheme.CartierDuality.CharacterSheaf.Construction.Schemes.multiplicativeGroupOver (Spec (.of k))).X))
    (he : e.toSheafPairing.IsPerfect)
    (hself : e.relativeAnnihilator (AbelianScheme.IsogenyQuotient.Intrinsic.MorphismKernel.Construction.nativeMorphismKernel (AbelianScheme.IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionMap n q)) =
      AbelianScheme.IsogenyQuotient.Intrinsic.MorphismKernel.Construction.nativeMorphismKernel (AbelianScheme.IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionMap n q)) :
    Nonempty ((IsMonHom.monoidHom q (Over.mk (𝟙 (Spec (.of k))))).ker ≃*
      (IsMonHom.monoidHom v (Over.mk (𝟙 (Spec (.of k))))).ker) := by
  let T : Over (Spec (.of k)) := Over.mk (𝟙 (Spec (.of k)))
  let qT := IsMonHom.monoidHom (AbelianScheme.IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionMap n q) T
  let vT := IsMonHom.monoidHom (AbelianScheme.IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionMap n v) T
  obtain ⟨hquot⟩ := PairingCharacters.geometric_self_annihilator_quotient_type e he
    (AbelianScheme.IsogenyQuotient.Intrinsic.MorphismKernel.Construction.nativeMorphismKernel (AbelianScheme.IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionMap n q))
    (Finite.EtaleKernelModels.finiteEtaleMorphismKernelModel (AbelianScheme.IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionMap n q)) hself
  have hr : qT.range = vT.ker :=
    PairedTorsionKernels.geometric_paired_torsion_image_kernel q v n hqv k (𝟙 (Spec (.of k)))
  let htor : qT.ker ≃* vT.ker := hquot.symm.trans
    ((QuotientGroup.quotientKerEquivRange qT).trans (MulEquiv.subgroupCongr hr))
  have hkq (x : T ⟶ A) (hx : x ≫ q = 1) : x ^ n = 1 := by
    calc
      x ^ n = x ≫ (𝟙 A) ^ n := by rw [MonObj.comp_pow, Category.comp_id]
      _ = x ≫ (q ≫ v) := by rw [hqv]
      _ = 1 := by rw [← Category.assoc, hx, MonObj.one_comp]
  have hkv (x : T ⟶ B) (hx : x ≫ v = 1) : x ^ n = 1 := by
    calc
      x ^ n = x ≫ (𝟙 B) ^ n := by rw [MonObj.comp_pow, Category.comp_id]
      _ = x ≫ (v ≫ q) := by rw [hvq]
      _ = 1 := by rw [← Category.assoc, hx, MonObj.one_comp]
  exact ⟨(nativeTorsionKernelPointEquiv q n T hkq).symm.trans
    (htor.trans (nativeTorsionKernelPointEquiv v n T hkv))⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Geometric.PairedKernelType
