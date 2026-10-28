import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.WeilCoverRefinement
import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.CartierEvaluationSquare

/-! # Weil Naturality Cover -/

namespace OAI.AlgebraicGeometry.AbelianScheme.TateComparison.WeilNaturalityCover

noncomputable section

/-! The canonical native Weil pairing respects original group maps
and their actual Picard dual pullbacks on every test scheme. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

universe u

private instance power_group {S : Scheme.{u}} (X : Over S) [GrpObj X] [IsCommMonObj X] (n : ℕ) :
    IsMonHom ((𝟙 X) ^ n) := Picard.Homomorphisms.GroupDescent.Construction.groupHom_pow_isMonHom (𝟙 X) n

section Groups
variable {S : Scheme.{u}} (A A' : Over S) [GrpObj A] [IsCommMonObj A] [GrpObj A'] [IsCommMonObj A']
  (t : A' ⟶ A) [IsMonHom t] (n : ℕ)

omit [IsCommMonObj A] [IsCommMonObj A'] in
theorem multiplicationCover_map : t ≫ ((𝟙 A) ^ n) = ((𝟙 A') ^ n) ≫ t := by
  rw [MonObj.comp_pow, MonObj.pow_comp, Category.comp_id, Category.id_comp]

theorem nativeWeilKernelPoint_map (T : Over S)
    (x : T ⟶ IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionScheme A n) (x' : T ⟶ IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionScheme A' n)
    (hx : (x' ≫ IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionInclusion A' n) ≫ t = x ≫ IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionInclusion A n) :
    WeilCoverRefinement.nativeWeilKernelPoint A' n T x' ≫
      KernelCharacterSquares.kernelSquareMap ((𝟙 A) ^ n) ((𝟙 A') ^ n) t t (multiplicationCover_map A A' t n) =
        WeilCoverRefinement.nativeWeilKernelPoint A n T x := by
  have : Mono (Picard.Homomorphisms.Kernel.Construction.kernelInclusion ((𝟙 A) ^ n)) :=
    inferInstanceAs (Mono (CategoryTheory.Limits.equalizer.ι ((𝟙 A) ^ n) 1))
  apply (cancel_mono (Picard.Homomorphisms.Kernel.Construction.kernelInclusion ((𝟙 A) ^ n))).mp
  rw [Category.assoc, KernelCharacterSquares.kernelSquareMap_inclusion, ← Category.assoc,
    WeilCoverRefinement.nativeWeilKernelPoint_inclusion, WeilCoverRefinement.nativeWeilKernelPoint_inclusion]
  exact hx

end Groups

variable {k : Type u} [Field k] [IsAlgClosed k]
  (A A' : Over (Spec (.of k)))
  [GrpObj A] [IsCommMonObj A] [Smooth A.hom] [IsProper A.hom] [GeometricallyConnected A.hom]
  [GrpObj A'] [IsCommMonObj A'] [Smooth A'.hom] [IsProper A'.hom] [GeometricallyConnected A'.hom]
  (D : Picard.Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData A) (D' : Picard.Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData A')
  (ell : A ⟶ D.abelian) [IsMonHom ell] [IsFinite ell.left] [Flat ell.left] [Surjective ell.left]
  (ell' : A' ⟶ D'.abelian) [IsMonHom ell'] [IsFinite ell'.left] [Flat ell'.left] [Surjective ell'.left]
  (n : ℕ) (hn : 0 < n)
  (hdegree : ∀ s : Spec (.of k), n.Coprime (ell.left.finrank (η[D.abelian].left s)))
  (hdegree' : ∀ s : Spec (.of k), n.Coprime (ell'.left.finrank (η[D'.abelian].left s)))
  (t : A' ⟶ A) [IsMonHom t] (d : D.abelian ⟶ D'.abelian) (hd : d = Picard.Homomorphisms.UnbundledDualPullback.Construction.UnbundledPicard.dualPicardPullback D' D t)

theorem nativeWeilPairing_character_value (T : Over (Spec (.of k)))
    (x : T ⟶ IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionScheme A n) (y : T ⟶ IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionScheme D.abelian n) :
    (IsogenyQuotient.Geometric.WeilPairing.Construction.geometricNativeWeilPairing A D ell n hn hdegree).pairValue x y =
      CartierDuality.Evaluation.Construction.CharacterEvaluation.value ((IsogenyQuotient.Canonical.CartierMap.Construction.multiplicationCartierRepresentation A D ell n hn).sectionEquiv T
        (CartierPairingCharacters.nativeWeilCharacterPoint A D ell n hn hdegree T y)) (WeilCoverRefinement.nativeWeilKernelPoint A n T x) :=
  IsogenyQuotient.Geometric.WeilPairing.Construction.geometricNativeWeilPairing_value A D ell n hn hdegree T x y

include hd in
theorem nativeWeilCharacterPoint_picard_map (T : Over (Spec (.of k)))
    (y : T ⟶ IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionScheme D.abelian n) (y' : T ⟶ IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionScheme D'.abelian n)
    (hy : (y ≫ IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionInclusion D.abelian n) ≫ d = y' ≫ IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionInclusion D'.abelian n) :
    (CartierPairingCharacters.nativeWeilCharacterPoint A D ell n hn hdegree T y ≫ CartierPairingCharacters.multiplicationPicardMap A D ell n hn) ≫
      Picard.Homomorphisms.UnbundledDualPullback.Construction.UnbundledPicard.dualPicardPullback D' D t =
        CartierPairingCharacters.nativeWeilCharacterPoint A' D' ell' n hn hdegree' T y' ≫ CartierPairingCharacters.multiplicationPicardMap A' D' ell' n hn := by
  have hh : (y ≫ IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionInclusion D.abelian n) ≫ Picard.Homomorphisms.UnbundledDualPullback.Construction.UnbundledPicard.dualPicardPullback D' D t =
      y' ≫ IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionInclusion D'.abelian n :=
    (congrArg (fun a => (y ≫ IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionInclusion D.abelian n) ≫ a) hd.symm).trans hy
  exact (congrArg (fun a => a ≫ Picard.Homomorphisms.UnbundledDualPullback.Construction.UnbundledPicard.dualPicardPullback D' D t)
      (CartierPairingCharacters.nativeWeilCharacterPoint_picard A D ell n hn hdegree T y)).trans
      (hh.trans (CartierPairingCharacters.nativeWeilCharacterPoint_picard A' D' ell' n hn hdegree' T y').symm)

include hd in
theorem nativeWeilCharacters_natural (T : Over (Spec (.of k)))
    (y : T ⟶ IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionScheme D.abelian n) (y' : T ⟶ IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionScheme D'.abelian n)
    (hy : (y ≫ IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionInclusion D.abelian n) ≫ d = y' ≫ IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionInclusion D'.abelian n) :
    ParameterCharacterSquares.squareCharacterSection ((𝟙 A) ^ n) ((𝟙 A') ^ n) t t (multiplicationCover_map A A' t n) T
      ((IsogenyQuotient.Canonical.CartierMap.Construction.multiplicationCartierRepresentation A D ell n hn).sectionEquiv T
        (CartierPairingCharacters.nativeWeilCharacterPoint A D ell n hn hdegree T y)) =
      (IsogenyQuotient.Canonical.CartierMap.Construction.multiplicationCartierRepresentation A' D' ell' n hn).sectionEquiv T
        (CartierPairingCharacters.nativeWeilCharacterPoint A' D' ell' n hn hdegree' T y') := by
  obtain ⟨hf, hflat, hs, hfp⟩ := CartierDuality.MultiplicationCovers.Construction.RelativeAbelian.positive_power_cover A D ell n hn
  obtain ⟨hf', hflat', hs', hfp'⟩ := CartierDuality.MultiplicationCovers.Construction.RelativeAbelian.positive_power_cover A' D' ell' n hn
  exact CartierEvaluationSquare.cartierCharacter_square ((𝟙 A) ^ n) ((𝟙 A') ^ n) t t
    (multiplicationCover_map A A' t n) D D'
    (IsogenyQuotient.Canonical.CartierMap.Construction.multiplicationCartierRepresentation A D ell n hn) (IsogenyQuotient.Canonical.CartierMap.Construction.multiplicationCartierRepresentation A' D' ell' n hn)
    T _ _ (nativeWeilCharacterPoint_picard_map A A' D D' ell ell' n hn hdegree hdegree' t d hd T y y' hy)

include hd in
theorem nativeWeilPairing_natural (T : Over (Spec (.of k)))
    (x : T ⟶ IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionScheme A n) (x' : T ⟶ IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionScheme A' n)
    (y : T ⟶ IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionScheme D.abelian n) (y' : T ⟶ IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionScheme D'.abelian n)
    (hx : (x' ≫ IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionInclusion A' n) ≫ t = x ≫ IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionInclusion A n)
    (hy : (y ≫ IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionInclusion D.abelian n) ≫ d = y' ≫ IsogenyQuotient.Torsion.Groups.Construction.nativeTorsionInclusion D'.abelian n) :
    (IsogenyQuotient.Geometric.WeilPairing.Construction.geometricNativeWeilPairing A' D' ell' n hn hdegree').pairValue x' y' =
      (IsogenyQuotient.Geometric.WeilPairing.Construction.geometricNativeWeilPairing A D ell n hn hdegree).pairValue x y := by
  let χ := (IsogenyQuotient.Canonical.CartierMap.Construction.multiplicationCartierRepresentation A D ell n hn).sectionEquiv T
    (CartierPairingCharacters.nativeWeilCharacterPoint A D ell n hn hdegree T y)
  let χ' := (IsogenyQuotient.Canonical.CartierMap.Construction.multiplicationCartierRepresentation A' D' ell' n hn).sectionEquiv T
    (CartierPairingCharacters.nativeWeilCharacterPoint A' D' ell' n hn hdegree' T y')
  let z := WeilCoverRefinement.nativeWeilKernelPoint A' n T x'
  have hχ := nativeWeilCharacters_natural A A' D D' ell ell' n hn hdegree hdegree' t d hd T y y' hy
  have hc : CartierDuality.Evaluation.Construction.CharacterEvaluation.value χ' z = CartierDuality.Evaluation.Construction.CharacterEvaluation.value χ
      (z ≫ KernelCharacterSquares.kernelSquareMap ((𝟙 A) ^ n) ((𝟙 A') ^ n) t t (multiplicationCover_map A A' t n)) :=
    (congrArg (fun ψ : (CartierDuality.CharacterSheaf.Construction.Schemes.characterSheaf (Spec (.of k))
      (Grp.mk (Picard.Homomorphisms.Kernel.Construction.kernelScheme ((𝟙 A') ^ n)))).obj.obj (.op T) => CartierDuality.Evaluation.Construction.CharacterEvaluation.value ψ z) hχ.symm).trans
      (ParameterCharacterSquares.squareCharacterSection_value ((𝟙 A) ^ n) ((𝟙 A') ^ n) t t (multiplicationCover_map A A' t n) T χ z)
  have hk := nativeWeilKernelPoint_map A A' t n T x x' hx
  exact (nativeWeilPairing_character_value A' D' ell' n hn hdegree' T x' y').trans
    (hc.trans ((congrArg (CartierDuality.Evaluation.Construction.CharacterEvaluation.value χ) hk).trans
      (nativeWeilPairing_character_value A D ell n hn hdegree T x y).symm))

end

end OAI.AlgebraicGeometry.AbelianScheme.TateComparison.WeilNaturalityCover
