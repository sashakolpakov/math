import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.CartierPairingCharacters

/-! # Weil Cover Refinement -/

namespace OAI.AlgebraicGeometry.AbelianScheme.TateComparison.WeilCoverRefinement

noncomputable section

/-! Canonical native Weil evaluation agrees along a refinement of
multiplication covers. The comparison is proved from actual character
descent and preserves the original torsion inclusions. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

universe u
section Groups
variable {S : Scheme.{u}} (A : Over S) [GrpObj A] [IsCommMonObj A]

private instance multiplication_isMonHom (n : ℕ) : IsMonHom ((𝟙 A) ^ n) :=
  Picard.Homomorphisms.GroupDescent.Construction.groupHom_pow_isMonHom (𝟙 A) n

omit [IsCommMonObj A] in
theorem multiplicationCover_refinement (n N m : ℕ) (hm : m * n = N) :
    ((𝟙 A) ^ m) ≫ ((𝟙 A) ^ n) = (𝟙 A) ^ N := by
  rw [MonObj.comp_pow, Category.comp_id, ← pow_mul, hm]

def nativeWeilKernelPoint (n : ℕ) (T : Over S) (x : T ⟶ IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionScheme A n) :
    T ⟶ Picard.Homomorphisms.Kernel.Construction.kernelScheme ((𝟙 A) ^ n) :=
  x ≫ (IsogenyQuotient.CharacterTorsionComparison.Construction.multiplicationKernelNativeGroupIso (Grp.mk A) n).inv.hom.hom

theorem nativeWeilKernelPoint_inclusion (n : ℕ) (T : Over S) (x : T ⟶ IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionScheme A n) :
    nativeWeilKernelPoint A n T x ≫ Picard.Homomorphisms.Kernel.Construction.kernelInclusion ((𝟙 A) ^ n) = x ≫ IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionInclusion A n :=
  CartierPairingCharacters.groupIso_inverse_point_composite (IsogenyQuotient.CharacterTorsionComparison.Construction.multiplicationKernelNativeGroupIso (Grp.mk A) n)
    x (Picard.Homomorphisms.Kernel.Construction.kernelInclusion ((𝟙 A) ^ n)) (IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionInclusion A n)
    (IsogenyQuotient.CharacterTorsionComparison.Construction.multiplicationKernelNativeGroupIso_inclusion (Grp.mk A) n)

theorem nativeWeilKernelPoint_refinement (n N m : ℕ) (hm : m * n = N)
    (T : Over S) (x : T ⟶ IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionScheme A n) (x' : T ⟶ IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionScheme A N)
    (hx : (x' ≫ IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionInclusion A N) ^ m = x ≫ IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionInclusion A n) :
    nativeWeilKernelPoint A N T x' ≫
      KernelCharacterSquares.kernelSquareMap ((𝟙 A) ^ n) ((𝟙 A) ^ N) (𝟙 A) ((𝟙 A) ^ m)
        ((multiplicationCover_refinement A n N m hm).trans (Category.comp_id _).symm) =
      nativeWeilKernelPoint A n T x := by
  have : Mono (Picard.Homomorphisms.Kernel.Construction.kernelInclusion ((𝟙 A) ^ n)) :=
    inferInstanceAs (Mono (CategoryTheory.Limits.equalizer.ι ((𝟙 A) ^ n) 1))
  apply (cancel_mono (Picard.Homomorphisms.Kernel.Construction.kernelInclusion ((𝟙 A) ^ n))).mp
  rw [Category.assoc, KernelCharacterSquares.kernelSquareMap_inclusion, ← Category.assoc,
    nativeWeilKernelPoint_inclusion, nativeWeilKernelPoint_inclusion, MonObj.comp_pow, Category.comp_id]
  exact hx

end Groups

variable {k : Type u} [Field k] [IsAlgClosed k]
  (A : Over (Spec (.of k))) [GrpObj A] [IsCommMonObj A]
  [Smooth A.hom] [IsProper A.hom] [GeometricallyConnected A.hom]
  (D : Picard.Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData A) (ell : A ⟶ D.abelian) [IsMonHom ell]
  [IsFinite ell.left] [Flat ell.left] [Surjective ell.left]
  (n : ℕ) (hn : 0 < n)
  (hdegree : ∀ s : Spec (.of k), n.Coprime (ell.left.finrank (η[D.abelian].left s)))
  (N : ℕ) (hN : 0 < N)
  (hdegreeN : ∀ s : Spec (.of k), N.Coprime (ell.left.finrank (η[D.abelian].left s)))
  (m : ℕ) (hm : m * n = N)

include hm in
theorem nativeWeilPairing_refinement (T : Over (Spec (.of k)))
    (x : T ⟶ IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionScheme A n) (x' : T ⟶ IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionScheme A N)
    (y : T ⟶ IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionScheme D.abelian n) (y' : T ⟶ IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionScheme D.abelian N)
    (hx : (x' ≫ IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionInclusion A N) ^ m = x ≫ IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionInclusion A n)
    (hy : y ≫ IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionInclusion D.abelian n = y' ≫ IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionInclusion D.abelian N) :
    (IsogenyQuotient.Geometric.WeilPairing.Construction.geometricNativeWeilPairing A D ell N hN hdegreeN).pairValue x' y' =
      (IsogenyQuotient.Geometric.WeilPairing.Construction.geometricNativeWeilPairing A D ell n hn hdegree).pairValue x y := by
  obtain ⟨hfn, hflatn, hsn, hfpn⟩ := CartierDuality.MultiplicationCovers.Construction.RelativeAbelian.positive_power_cover A D ell n hn
  obtain ⟨hfN, hflatN, hsN, hfpN⟩ := CartierDuality.MultiplicationCovers.Construction.RelativeAbelian.positive_power_cover A D ell N hN
  let z := CartierPairingCharacters.nativeWeilCharacterPoint A D ell n hn hdegree T y
  let z' := CartierPairingCharacters.nativeWeilCharacterPoint A D ell N hN hdegreeN T y'
  have hz : z ≫ CartierDuality.ParameterizedCharacterLines.Construction.KernelCharacters.cartierToPicard ((𝟙 A) ^ n) D (IsogenyQuotient.Canonical.CartierMap.Construction.multiplicationCartierRepresentation A D ell n hn) =
      z' ≫ CartierDuality.ParameterizedCharacterLines.Construction.KernelCharacters.cartierToPicard ((𝟙 A) ^ N) D (IsogenyQuotient.Canonical.CartierMap.Construction.multiplicationCartierRepresentation A D ell N hN) :=
    (CartierPairingCharacters.nativeWeilCharacterPoint_picard A D ell n hn hdegree T y).trans
      (hy.trans (CartierPairingCharacters.nativeWeilCharacterPoint_picard A D ell N hN hdegreeN T y').symm)
  have hc := CartierEvaluationRefinement.cartierEvaluation_refinement ((𝟙 A) ^ n) ((𝟙 A) ^ N) ((𝟙 A) ^ m)
    (multiplicationCover_refinement A n N m hm) D
    (IsogenyQuotient.Canonical.CartierMap.Construction.multiplicationCartierRepresentation A D ell n hn) (IsogenyQuotient.Canonical.CartierMap.Construction.multiplicationCartierRepresentation A D ell N hN)
    T z z' hz (nativeWeilKernelPoint A N T x')
  have hk := nativeWeilKernelPoint_refinement A n N m hm T x x' hx
  exact (IsogenyQuotient.Geometric.WeilPairing.Construction.geometricNativeWeilPairing_value A D ell N hN hdegreeN T x' y').trans
    (hc.trans ((congrArg ((IsogenyQuotient.Canonical.CartierMap.Construction.multiplicationCartierRepresentation A D ell n hn).evaluationValue T z) hk).trans
      (IsogenyQuotient.Geometric.WeilPairing.Construction.geometricNativeWeilPairing_value A D ell n hn hdegree T x y).symm))

include hm in
theorem nativeWeilPairing_power_refinement (T : Over (Spec (.of k)))
    (x : T ⟶ IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionScheme A n) (x' : T ⟶ IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionScheme A N)
    (y : T ⟶ IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionScheme D.abelian n) (y' : T ⟶ IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionScheme D.abelian N)
    (hx : (x' ≫ IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionInclusion A N) ^ m = x ≫ IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionInclusion A n)
    (hy : (y' ≫ IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionInclusion D.abelian N) ^ m = y ≫ IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionInclusion D.abelian n) :
    ((IsogenyQuotient.Geometric.WeilPairing.Construction.geometricNativeWeilPairing A D ell N hN hdegreeN).pairValue x' y') ^ m =
      (IsogenyQuotient.Geometric.WeilPairing.Construction.geometricNativeWeilPairing A D ell n hn hdegree).pairValue x y := by
  have hy' : y ≫ IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionInclusion D.abelian n =
      (y' ^ m) ≫ IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionInclusion D.abelian N :=
    hy.symm.trans (MonObj.pow_comp y' m (IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionInclusion D.abelian N)).symm
  exact ((IsogenyQuotient.Geometric.WeilPairing.Construction.geometricNativeWeilPairing A D ell N hN hdegreeN).pairRightHom x').map_pow y' m |>.symm.trans
    (nativeWeilPairing_refinement A D ell n hn hdegree N hN hdegreeN m hm T x x' y (y' ^ m) hx hy')

end

end OAI.AlgebraicGeometry.AbelianScheme.TateComparison.WeilCoverRefinement
