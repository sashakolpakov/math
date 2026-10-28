import OAI.NumberTheory.PadicHodge.IntegralComparison.PrincipalPoint.Source
import OAI.NumberTheory.PadicHodge.IntegralComparison.Affine.ResolutionCechRefinement

/-! # Pulled Integer Refinement -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.PrincipalPoint.PulledIntegerRefinement

noncomputable section

/-! The original point-comparison covers, pulled to an affine source,
satisfy the chosen integer-resolution refinement hypotheses. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.TopologicalSpace _root_.HomologicalComplex
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {Y X Z T : Scheme.{0}} [X.IsSeparated] [Z.IsSeparated]
  (f : Y ⟶ X) [IsAffineHom f] (i : X ⟶ Z) [IsClosedImmersion i]
  (s₀ : T ⟶ X) [IsClosedImmersion s₀]
  (U : Z.Opens) (hU : IsAffineOpen U) (hcontains : ⊤ ≤ (s₀ ≫ i) ⁻¹ᵁ U)
  {c g : ℕ} (s : Fin c → Γ(Z,U)) (t : Fin g → Γ(Z,U))
  (hs : Ideal.span (Set.range s) = i.ker.ideal ⟨U,hU⟩)
  (hst : Ideal.span (Set.range (Fin.append s t)) = (s₀ ≫ i).ker.ideal ⟨U,hU⟩)
  {κ : Type} [LinearOrder κ] (V : κ → Z.Opens)
  (hV : iSup V = ⊤) (haV : ∀ j, IsAffineOpen (V j))

include f in
private theorem source_separated : Y.IsSeparated := ⟨by
  rw [← terminal.comp_from f]
  infer_instance⟩

abbrev ambient := (RelativeCech.ReindexData.preimage (f ≫ i).base).obj (Principal.RelativeConcentration.ambient U hU)
abbrev complement := (RelativeCech.ReindexData.preimage (f ≫ i).base).obj ∘ RelativeGeometry.complementary i s₀
abbrev common := (RelativeCech.ReindexData.preimage (f ≫ i).base).obj ∘ RelativeGeometry.common i s₀ U hU t
abbrev localRight := RelativeCech.Reindex.mapped (f ≫ i).base (RelativeGeometry.complementary i s₀)
  (RelativeGeometry.common i s₀ U hU t)
  (RelativeGeometry.right i s₀ U hU t)
abbrev outside := f ⁻¹ᵁ SectionIdealPuncturedCover.outside s₀.ker
abbrev sourceOutside := f ⁻¹ᵁ RelativeGeometry.sourceOutside i s₀ U
abbrev global := (RelativeCech.ReindexData.preimage (f ≫ i).base).obj ∘ V
abbrev globalCommon := (RelativeCech.ReindexData.preimage (f ≫ i).base).obj ∘
  PointComplementGlobalCover.common (s₀ ≫ i) (Principal.RelativeConcentration.ambient U hU) V
abbrev globalRight := RelativeCech.ReindexGlobal.rightRefinement (f ≫ i).base V
  (PointComplementGlobalCover.common (s₀ ≫ i) (Principal.RelativeConcentration.ambient U hU) V)
  (PointComplementGlobalCover.right (s₀ ≫ i) (Principal.RelativeConcentration.ambient U hU) V)

omit [X.IsSeparated] [Z.IsSeparated] in
theorem ambient_affine : IsAffineOpen (ambient f i U hU) :=
  (Principal.RelativeConcentration.ambient_affine U hU).preimage (f ≫ i)

omit [X.IsSeparated] [Z.IsSeparated] [IsClosedImmersion s₀] in
theorem complement_affine (j : ComplementaryAffineCover.Index
    (RelativeGeometry.outside i s₀)) : IsAffineOpen (complement f i s₀ j) :=
  (RelativeGeometry.complementary_affine i s₀ j).preimage (f ≫ i)

omit [X.IsSeparated] [IsClosedImmersion s₀] in
theorem common_affine (j : RelativeGeometry.CommonIndex (g := g) i s₀) :
    IsAffineOpen (common f i s₀ U hU t j) :=
  (RelativeGeometry.common_affine i s₀ U hU t j).preimage (f ≫ i)

omit [X.IsSeparated] [Z.IsSeparated] [IsAffineHom f] in
theorem complement_below (j : ComplementaryAffineCover.Index
    (RelativeGeometry.outside i s₀)) : complement f i s₀ j ≤ outside f s₀ := by
  have h := (Opens.map (f ≫ i).base).monotone
    (RelativeGeometry.complementary_outside i s₀ j)
  simpa only [complement, outside, Function.comp_apply, RelativeCech.ReindexData.preimage,
    Scheme.Hom.comp_preimage, Closed.PointParameterCover.outside] using h

omit [X.IsSeparated] [Z.IsSeparated] [IsAffineHom f] in
theorem complementary_cover :
    (⨆ j, ambient f i U hU ⊓ complement f i s₀ j) = sourceOutside f i s₀ U := by
  have h := congrArg (fun A : X.Opens => f ⁻¹ᵁ A)
    (RelativeGeometry.complementary_cover i s₀ U hU)
  change (⨆ j, (f ≫ i) ⁻¹ᵁ (Principal.RelativeConcentration.ambient U hU) ⊓
    (f ≫ i) ⁻¹ᵁ (RelativeGeometry.complementary i s₀ j)) = _
  simpa only [sourceOutside, Scheme.Hom.comp_preimage,
    Scheme.Hom.preimage_iSup, Scheme.Hom.preimage_inf] using h

include hs hst in
omit [X.IsSeparated] [Z.IsSeparated] [IsAffineHom f] in
theorem common_cover :
    (⨆ j, ambient f i U hU ⊓ common f i s₀ U hU t j) = sourceOutside f i s₀ U := by
  have h := congrArg (fun A : X.Opens => f ⁻¹ᵁ A)
    (RelativeGeometry.common_cover i s₀ U hU s t hs hst)
  change (⨆ j, (f ≫ i) ⁻¹ᵁ (Principal.RelativeConcentration.ambient U hU) ⊓
    (f ≫ i) ⁻¹ᵁ (RelativeGeometry.common i s₀ U hU t j)) = _
  simpa only [sourceOutside, Scheme.Hom.comp_preimage,
    Scheme.Hom.preimage_iSup, Scheme.Hom.preimage_inf] using h

include hV in
omit [X.IsSeparated] [Z.IsSeparated] [IsAffineHom f] [IsClosedImmersion i] [LinearOrder κ] in
theorem global_cover : iSup (global f i V) = ⊤ := by
  change (⨆ j, (f ≫ i) ⁻¹ᵁ V j) = ⊤
  rw [← Scheme.Hom.preimage_iSup, hV]
  rfl

include haV in
omit [X.IsSeparated] [Z.IsSeparated] [LinearOrder κ] in
theorem global_affine (j : κ) : IsAffineOpen (global f i V j) := (haV j).preimage (f ≫ i)

include hcontains hV in
omit [X.IsSeparated] [Z.IsSeparated] [IsAffineHom f] [LinearOrder κ] in
theorem globalCommon_cover : iSup (globalCommon f i s₀ U hU V) = ⊤ := by
  change (⨆ j, (f ≫ i) ⁻¹ᵁ
    PointComplementGlobalCover.common (s₀ ≫ i) (Principal.RelativeConcentration.ambient U hU) V j) = ⊤
  rw [← Scheme.Hom.preimage_iSup,
    PointComplementGlobalCover.common_covers (s₀ ≫ i) (Principal.RelativeConcentration.ambient U hU)
      (PrincipalReference.CoverTransfer.Reference.contains U hU (s₀ ≫ i) hcontains) V hV]
  rfl

include haV in
omit [X.IsSeparated] [IsClosedImmersion s₀] [LinearOrder κ] in
theorem globalCommon_affine (j : PointComplementGlobalCover.CommonIndex (ι := κ) (s₀ ≫ i)) :
    IsAffineOpen (globalCommon f i s₀ U hU V j) :=
  (PointComplementGlobalCover.common_affine (s₀ ≫ i) (Principal.RelativeConcentration.ambient U hU)
    (Principal.RelativeConcentration.ambient_affine U hU) V haV j).preimage (f ≫ i)

variable (N : Y.Modules) [N.IsQuasicoherent] (d q : ℕ)

include hs hst in
theorem relative_integer : IsIso (RelativeCech.Refinement.homology (ambient f i U hU)
    (complement f i s₀) (common f i s₀ U hU t) (localRight f i s₀ U hU t)
    (Affine.OrderedInjective.Comparison.integerPresheaf N d) q) := by
  let := source_separated f
  exact Affine.ResolutionCechRefinement.relative_integer (ambient f i U hU) (ambient_affine f i U hU)
    (complement f i s₀) (common f i s₀ U hU t) (localRight f i s₀ U hU t)
    (sourceOutside f i s₀ U) (complementary_cover f i s₀ U hU) (common_cover f i s₀ U hU s t hs hst)
    (complement_affine f i s₀) (common_affine f i s₀ U hU t) N d q

include hcontains hV haV in
theorem ordered_integer : IsIso (homologyMap (OrderedCech.Refinement.totalMap (global f i V)
    (globalCommon f i s₀ U hU V) (globalRight f i s₀ U hU V)
    (Affine.OrderedInjective.Comparison.integerPresheaf N d)) q) := by
  let := source_separated f
  exact Affine.ResolutionCechRefinement.ordered_integer (global f i V)
    (globalCommon f i s₀ U hU V) (globalRight f i s₀ U hU V)
    (global_affine f i V haV) (globalCommon_affine f i s₀ U hU V haV) N d
    (global_cover f i V hV) (globalCommon_cover f i s₀ U hU hcontains V hV) q

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.PrincipalPoint.PulledIntegerRefinement
