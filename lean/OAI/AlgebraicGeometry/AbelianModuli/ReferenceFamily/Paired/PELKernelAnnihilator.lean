import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Paired.PELPairingAdjoints
import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.PairingNondegeneracy
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Intrinsic.MorphismKernel

/-! # PEL Kernel Annihilator -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Paired.PELKernelAnnihilator

noncomputable section

section

/-! The complementary kernel is self-annihilating for the actual
target pairing. One direction uses perfection of the source pairing;
the other uses the actual finite-flat pullback cover of the isogeny. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Intrinsic.MorphismKernel.Construction

theorem nativeTorsionMap_kernel_point_iff
    {S : Scheme.{0}} {A B : Over S} [GrpObj A] [GrpObj B]
    [IsCommMonObj A] [IsCommMonObj B] (v : B ⟶ A) [IsMonHom v]
    (n : ℕ) (T : Over S) (y : T ⟶ AbelianScheme.IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionScheme B n) :
    y ≫ AbelianScheme.IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionMap n v = 1 ↔ (y ≫ AbelianScheme.IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionInclusion B n) ≫ v = 1 := by
  rw [← cancel_mono (AbelianScheme.IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionInclusion A n), Category.assoc,
    AbelianScheme.IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionMap_inclusion, ← Category.assoc, MonObj.one_comp]

theorem nativeTorsionMap_kernel_eq
    {S : Scheme.{0}} {A B : Over S} [GrpObj A] [GrpObj B]
    [IsCommMonObj A] [IsCommMonObj B] (v : B ⟶ A) [IsMonHom v] (n : ℕ) :
    AbelianScheme.IsogenyQuotient.Intrinsic.MorphismKernel.Construction.nativeMorphismKernel (AbelianScheme.IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionMap n v) =
      AbelianScheme.IsogenyQuotient.SubgroupTransport.Construction.relativeSubgroupPullback (AbelianScheme.IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionInclusion B n) (AbelianScheme.IsogenyQuotient.Intrinsic.MorphismKernel.Construction.nativeMorphismKernel v) := by
  ext T t y
  exact nativeTorsionMap_kernel_point_iff v n T y

theorem schemePairing_nondegenerate_right
    {S : Scheme.{0}} {A B : Over S} [GrpObj A] [GrpObj B]
    [IsCommMonObj A] [IsCommMonObj B]
    (e : AbelianScheme.IsogenyQuotient.Annihilator.Construction.SchemeBicharacter (A := A) (B := B) (W := (AbelianScheme.CartierDuality.CharacterSheaf.Construction.Schemes.multiplicativeGroupOver S).X))
    (he : e.toSheafPairing.IsPerfect) (T : Over S) (y : T ⟶ B)
    (hy : ∀ (U : Over S) (b : U ⟶ T) (x : U ⟶ A), e.pairValue x (b ≫ y) = 1) : y = 1 := by
  have hf : e.flip.toSheafPairing.IsPerfect := by
    rw [e.toSheafPairing_flip]
    refine ⟨he.2, ?_⟩
    have h : e.toSheafPairing.flip.rightAdjoint = e.toSheafPairing.leftAdjoint :=
      congrArg AbelianScheme.CartierDuality.SheafEvaluation.Construction.Schemes.BilinearPairing.leftAdjoint (AbelianScheme.CartierDuality.SheafEvaluation.Construction.Schemes.BilinearPairing.flip_flip e.toSheafPairing)
    exact h.symm ▸ he.1
  apply AbelianScheme.TateComparison.PairingNondegeneracy.schemePairing_nondegenerate_left e.flip hf T y
  intro U b x
  rw [e.flip_pairValue]
  exact hy U b x

theorem paired_torsion_kernel_self_annihilating
    {S : Scheme.{0}} {A B : Over S} [GrpObj A] [GrpObj B]
    [IsCommMonObj A] [IsCommMonObj B]
    (q : A ⟶ B) [IsMonHom q] [IsFinite q.left] [Flat q.left] [Surjective q.left]
    (v : B ⟶ A) [IsMonHom v] (n : ℕ)
    (hqv : q ≫ v = (𝟙 A) ^ n)
    (eA : AbelianScheme.IsogenyQuotient.Annihilator.Construction.SchemeBicharacter (A := AbelianScheme.IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionScheme A n)
      (B := AbelianScheme.IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionScheme A n) (W := (AbelianScheme.CartierDuality.CharacterSheaf.Construction.Schemes.multiplicativeGroupOver S).X))
    (eB : AbelianScheme.IsogenyQuotient.Annihilator.Construction.SchemeBicharacter (A := AbelianScheme.IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionScheme B n)
      (B := AbelianScheme.IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionScheme B n) (W := (AbelianScheme.CartierDuality.CharacterSheaf.Construction.Schemes.multiplicativeGroupOver S).X))
    (heA : eA.toSheafPairing.IsPerfect)
    (hadjoint : ∀ (T : Over S) (x : T ⟶ AbelianScheme.IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionScheme A n)
      (y : T ⟶ AbelianScheme.IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionScheme B n),
      eB.pairValue (x ≫ AbelianScheme.IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionMap n q) y =
        eA.pairValue x (y ≫ AbelianScheme.IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionMap n v)) :
    eB.relativeAnnihilator (AbelianScheme.IsogenyQuotient.Intrinsic.MorphismKernel.Construction.nativeMorphismKernel (AbelianScheme.IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionMap n v)) =
      AbelianScheme.IsogenyQuotient.Intrinsic.MorphismKernel.Construction.nativeMorphismKernel (AbelianScheme.IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionMap n v) := by
  have himage (T : Over S) (x : T ⟶ AbelianScheme.IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionScheme A n) :
      (x ≫ AbelianScheme.IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionMap n q) ≫ AbelianScheme.IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionMap n v = 1 := by
    apply (nativeTorsionMap_kernel_point_iff v n T _).mpr
    calc
      ((x ≫ AbelianScheme.IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionMap n q) ≫ AbelianScheme.IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionInclusion B n) ≫ v =
          (x ≫ AbelianScheme.IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionInclusion A n) ≫ (q ≫ v) := by
        simp only [Category.assoc, AbelianScheme.IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionMap_inclusion]
      _ = (x ≫ AbelianScheme.IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionInclusion A n) ^ n := by
        rw [hqv, MonObj.comp_pow, Category.comp_id]
      _ = 1 := by rw [← MonObj.comp_pow, AbelianScheme.IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionInclusion_killed, MonObj.comp_one]
  ext T t y
  change (∀ (U : Over S) (b : U ⟶ T) (x : U ⟶ AbelianScheme.IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionScheme B n),
    x ≫ AbelianScheme.IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionMap n v = 1 → eB.pairValue x (b ≫ y) = 1) ↔
      y ≫ AbelianScheme.IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionMap n v = 1
  constructor
  · intro hy
    apply schemePairing_nondegenerate_right eA heA T (y ≫ AbelianScheme.IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionMap n v)
    intro U b x
    have h := (hadjoint U x (b ≫ y)).symm.trans
      (hy U b (x ≫ AbelianScheme.IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionMap n q) (himage U x))
    simpa only [Category.assoc] using h
  · intro hy U b x hx
    let Z := pullback q (x ≫ AbelianScheme.IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionInclusion B n)
    let a : Z ⟶ A := pullback.fst q (x ≫ AbelianScheme.IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionInclusion B n)
    let c : Z ⟶ U := pullback.snd q (x ≫ AbelianScheme.IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionInclusion B n)
    have hs : IsPullback a.left c.left q.left (x ≫ AbelianScheme.IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionInclusion B n).left :=
      (IsPullback.of_hasPullback q (x ≫ AbelianScheme.IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionInclusion B n)).map (Over.forget S)
    let : IsFinite c.left := MorphismProperty.of_isPullback hs inferInstance
    let : Flat c.left := MorphismProperty.of_isPullback hs inferInstance
    let : Surjective c.left := MorphismProperty.of_isPullback hs inferInstance
    let : EffectiveEpi c := PELModuli.IntegralModel.IsogenyFactorizationIs.IsogenyFactorization.effectiveEpi_over_of_fpqc c
    have hc : a ≫ q = c ≫ (x ≫ AbelianScheme.IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionInclusion B n) := pullback.condition
    have hxa := (nativeTorsionMap_kernel_point_iff v n U x).mp hx
    have ha : a ^ n = 1 := by
      calc
        a ^ n = a ≫ (𝟙 A) ^ n := by rw [MonObj.comp_pow, Category.comp_id]
        _ = a ≫ (q ≫ v) := by rw [hqv]
        _ = c ≫ ((x ≫ AbelianScheme.IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionInclusion B n) ≫ v) := by
          rw [← Category.assoc, hc, Category.assoc]
        _ = 1 := by rw [hxa, MonObj.comp_one]
    let z := AbelianScheme.IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionLift A n a ha
    have hz : z ≫ AbelianScheme.IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionMap n q = c ≫ x := by
      apply (cancel_mono (AbelianScheme.IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionInclusion B n)).mp
      rw [Category.assoc, AbelianScheme.IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionMap_inclusion, ← Category.assoc,
        AbelianScheme.IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionLift_inclusion, Category.assoc]
      exact hc
    apply (cancel_epi c).mp
    calc
      c ≫ eB.pairValue x (b ≫ y) = eB.pairValue (c ≫ x) (c ≫ (b ≫ y)) :=
        (eB.pairValue_natural c x (b ≫ y)).symm
      _ = eA.pairValue z ((c ≫ (b ≫ y)) ≫ AbelianScheme.IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionMap n v) := by
        rw [← hz]
        exact hadjoint Z z (c ≫ (b ≫ y))
      _ = 1 := by
        rw [Category.assoc, Category.assoc, hy, MonObj.comp_one, MonObj.comp_one]
        exact eA.one_right Z z
      _ = c ≫ 1 := (MonObj.comp_one c).symm

end

/-! Both actual kernels in a paired PEL quotient equal their own
annihilators for the original canonical polarization pairings. The
only degree condition is the prescribed coprimality at the multiplier. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped BigOperators

open OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Intrinsic.MorphismKernel.Construction

variable {E K : Type} [Field E] [NumberField E] [Algebra ℚ E]
    [NumberField.IsCMField E] [Field K]
    {s N n : ℕ} {P : Datum.RankThreePELDatum E s} {iota : E →+* K}
    {T : Over (Spec (.of K))} [IsLocallyNoetherian T.left]
    {A B : PEL.Objects.PELObject P iota N T}

theorem pairedPELQuotient_reverse_kernel_self_annihilating
    (f : PELQuotients.PairedPELQuotient A B n) (hn : 0 < n)
    (hdegree : Nat.Coprime n ((∏ i, P.polarizationType i) ^ 2)) :
    let H := AbelianScheme.IsogenyQuotient.SubgroupTransport.Construction.relativeSubgroupPullback (AbelianScheme.IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionInclusion B.polarized.abelian.scheme n)
      (AbelianScheme.IsogenyQuotient.Intrinsic.MorphismKernel.Construction.nativeMorphismKernel f.reverse.isogeny.hom)
    (AbelianScheme.IsogenyQuotient.Noetherian.PolarizationAdapter.Construction.noetherianNativePolarizationPairing B.polarized.abelian B.polarized.dual
      B.polarized.polarization n hn).relativeAnnihilator H = H := by
  have h := paired_torsion_kernel_self_annihilating f.forward.isogeny.hom f.reverse.isogeny.hom
    n f.forward_reverse
    (AbelianScheme.IsogenyQuotient.Noetherian.PolarizationAdapter.Construction.noetherianNativePolarizationPairing A.polarized.abelian A.polarized.dual A.polarized.polarization n hn)
    (AbelianScheme.IsogenyQuotient.Noetherian.PolarizationAdapter.Construction.noetherianNativePolarizationPairing B.polarized.abelian B.polarized.dual B.polarized.polarization n hn)
    (AbelianScheme.IsogenyQuotient.Noetherian.PolarizationAdapter.Construction.noetherianNativePolarizationPairing_isPerfect A.polarized.abelian A.polarized.dual
      A.polarized.polarization n hn hdegree)
    (PELPairingAdjoints.pairedPELQuotient_pairing_adjoint f n hn)
  rw [nativeTorsionMap_kernel_eq] at h
  exact h

theorem pairedPELQuotient_forward_kernel_self_annihilating
    (f : PELQuotients.PairedPELQuotient A B n) (hn : 0 < n)
    (hdegree : Nat.Coprime n ((∏ i, P.polarizationType i) ^ 2)) :
    let H := AbelianScheme.IsogenyQuotient.SubgroupTransport.Construction.relativeSubgroupPullback (AbelianScheme.IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionInclusion A.polarized.abelian.scheme n)
      (AbelianScheme.IsogenyQuotient.Intrinsic.MorphismKernel.Construction.nativeMorphismKernel f.forward.isogeny.hom)
    (AbelianScheme.IsogenyQuotient.Noetherian.PolarizationAdapter.Construction.noetherianNativePolarizationPairing A.polarized.abelian A.polarized.dual
      A.polarized.polarization n hn).relativeAnnihilator H = H :=
  pairedPELQuotient_reverse_kernel_self_annihilating f.swap hn hdegree

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Paired.PELKernelAnnihilator
