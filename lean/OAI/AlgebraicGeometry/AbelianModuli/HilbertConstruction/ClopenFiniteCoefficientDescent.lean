import Mathlib.AlgebraicGeometry.AffineTransitionLimit
import OAI.ArithmeticGeometry.Descent.CMVariety.FiniteCoefficientFst

/-! # Clopen Finite Coefficient Descent -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ClopenFiniteCoefficientDescent

noncomputable section

/-! A quasi-compact open whose pullback to an affine-transition limit
is closed becomes closed at a finite stage. Both the open and its
complement are descended; no flatness or reducedness is assumed. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.TopologicalSpace

universe u

theorem quasiCompactOpen_eventually_closed
    {I : Type u} [Category.{u} I] [IsCofiltered I]
    (D : I ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
    [∀ {i j : I} (f : i ⟶ j), IsAffineHom (D.map f)]
    [∀ i : I, CompactSpace (D.obj i)]
    [∀ i : I, QuasiSeparatedSpace (D.obj i)]
    (i : I) (U : (D.obj i).Opens) (hU : IsCompact (U : Set (D.obj i)))
    (hclosed : IsClosed ((c.π.app i ⁻¹ᵁ U : c.pt.Opens) : Set c.pt)) :
    ∃ (j : I) (f : j ⟶ i), IsClosed (D.map f ⁻¹ᵁ U : Set (D.obj j)) := by
  classical
  let : CompactSpace c.pt := Scheme.compactSpace_of_isLimit D c hc
  let V : c.pt.Opens := ⟨((c.π.app i ⁻¹ᵁ U : c.pt.Opens) : Set c.pt)ᶜ,
    hclosed.isOpen_compl⟩
  have hV : IsCompact (V : Set c.pt) :=
    (c.π.app i ⁻¹ᵁ U : c.pt.Opens).isOpen.isClosed_compl.isCompact
  obtain ⟨j, W, hW, hWV⟩ := exists_preimage_eq D c hc V hV
  let k := IsCofiltered.min i j
  let fi : k ⟶ i := IsCofiltered.minToLeft i j
  let fj : k ⟶ j := IsCofiltered.minToRight i j
  let U₀ := D.map fi ⁻¹ᵁ U
  let W₀ := D.map fj ⁻¹ᵁ W
  have hU₀ : IsCompact (U₀ : Set (D.obj k)) :=
    QuasiCompact.isCompact_preimage (f := D.map fi) _ U.isOpen hU
  have hW₀ : IsCompact (W₀ : Set (D.obj k)) :=
    QuasiCompact.isCompact_preimage (f := D.map fj) _ W.isOpen hW
  have hUi : c.π.app k ⁻¹ᵁ U₀ = c.π.app i ⁻¹ᵁ U := by
    change c.π.app k ⁻¹ᵁ (D.map fi ⁻¹ᵁ U) = _
    rw [← Scheme.Hom.comp_preimage, c.w fi]
  have hWj : c.π.app k ⁻¹ᵁ W₀ = V := by
    change c.π.app k ⁻¹ᵁ (D.map fj ⁻¹ᵁ W) = _
    rw [← Scheme.Hom.comp_preimage, c.w fj, hWV]
  have hcover : c.π.app k ⁻¹ᵁ (U₀ ⊔ W₀) = ⊤ := by
    rw [Scheme.Hom.preimage_sup, hUi, hWj]
    ext x
    simp [V]
  have hdisjoint : c.π.app k ⁻¹ᵁ (U₀ ⊓ W₀) = c.π.app k ⁻¹ᵁ ⊥ := by
    rw [Scheme.Hom.preimage_inf, hUi, hWj, Scheme.Hom.preimage_bot]
    ext x
    simp [V]
  obtain ⟨k₁, f₁, h₁⟩ := exists_map_eq_top D c hc (U₀ ⊔ W₀) hcover
  have hinter : IsCompact (U₀ ⊓ W₀ : Set (D.obj k)) :=
    hU₀.inter_of_isOpen hW₀ U₀.isOpen W₀.isOpen
  obtain ⟨k₂, f₂, h₂⟩ := exists_map_preimage_eq_map_preimage D c hc hinter
    (show IsCompact ((⊥ : (D.obj k).Opens) : Set (D.obj k)) from isCompact_empty) hdisjoint
  obtain ⟨l, g₁, g₂, hg⟩ := IsCofiltered.cospan f₁ f₂
  let U₁ := D.map (g₁ ≫ f₁) ⁻¹ᵁ U₀
  let W₁ := D.map (g₁ ≫ f₁) ⁻¹ᵁ W₀
  have hcover' : U₁ ⊔ W₁ = ⊤ := by
    change D.map (g₁ ≫ f₁) ⁻¹ᵁ U₀ ⊔ D.map (g₁ ≫ f₁) ⁻¹ᵁ W₀ = ⊤
    rw [← Scheme.Hom.preimage_sup, Functor.map_comp, Scheme.Hom.comp_preimage,
      h₁, Scheme.Hom.preimage_top]
  have hdisjoint' : U₁ ⊓ W₁ = ⊥ := by
    change D.map (g₁ ≫ f₁) ⁻¹ᵁ U₀ ⊓ D.map (g₁ ≫ f₁) ⁻¹ᵁ W₀ = ⊥
    rw [← Scheme.Hom.preimage_inf, hg, Functor.map_comp, Scheme.Hom.comp_preimage, h₂]
    simp only [Scheme.Hom.preimage_bot]
  have he : (U₁ : Set (D.obj l)) = (W₁ : Set (D.obj l))ᶜ := by
    have hs : (U₁ : Set (D.obj l)) ∪ (W₁ : Set (D.obj l)) = Set.univ :=
      congrArg (fun O : (D.obj l).Opens => (O : Set (D.obj l))) hcover'
    have hi : (U₁ : Set (D.obj l)) ∩ (W₁ : Set (D.obj l)) = ∅ :=
      congrArg (fun O : (D.obj l).Opens => (O : Set (D.obj l))) hdisjoint'
    ext x
    constructor
    · intro hx hy
      have hxy : x ∈ (U₁ : Set (D.obj l)) ∩ (W₁ : Set (D.obj l)) := ⟨hx, hy⟩
      rw [hi] at hxy
      exact hxy
    · intro hx
      have hxy : x ∈ (U₁ : Set (D.obj l)) ∪ (W₁ : Set (D.obj l)) := by
        rw [hs]
        trivial
      exact hxy.elim id (fun hy => (hx hy).elim)
  have hU₁ : IsClosed (U₁ : Set (D.obj l)) := by
    rw [he]
    exact W₁.isOpen.isClosed_compl
  refine ⟨l, (g₁ ≫ f₁) ≫ fi, ?_⟩
  rw [Functor.map_comp, Scheme.Hom.comp_preimage]
  exact hU₁

theorem finiteCoefficientOpen_eventually_closed
    (R B : Type) [CommRing R] [CommRing B] [Algebra R B]
    {Y : Scheme} (f : Y ⟶ Spec (.of R)) [QuasiCompact f] [QuasiSeparated f]
    (U : Y.Opens) (hU : IsCompact (U : Set Y))
    (hclosed : IsClosed (pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap R B))) f ⁻¹ᵁ U :
      Set (pullback (Spec.map (CommRingCat.ofHom (algebraMap R B))) f : Scheme))) :
    ∃ s : Finset B, IsClosed (pullback.snd (ArithmeticGeometry.Descent.CMVariety.FiniteCoefficientDiagram.Abelian.finiteCoefficientBaseMap R B s) f ⁻¹ᵁ U :
      Set (pullback (ArithmeticGeometry.Descent.CMVariety.FiniteCoefficientDiagram.Abelian.finiteCoefficientBaseMap R B s) f : Scheme)) := by
  let D := ArithmeticGeometry.Descent.CMVariety.FiniteCoefficientFst.Abelian.finiteCoefficientFamilyDiagram R B f
  let c := ArithmeticGeometry.Descent.CMVariety.FiniteCoefficientFst.Abelian.finiteCoefficientFamilyCone R B f
  let τ := ArithmeticGeometry.Descent.CMVariety.FiniteCoefficientFst.Abelian.finiteCoefficientFamilyStructure R B f
  let i : (Finset B)ᵒᵖ := .op ∅
  let V := τ.app i ⁻¹ᵁ U
  have hbase : IsAffineHom (ArithmeticGeometry.Descent.CMVariety.FiniteCoefficientDiagram.Abelian.finiteCoefficientBaseMap R B ∅) := by
    change IsAffineHom (Spec.map _)
    infer_instance
  let : IsAffineHom (τ.app i) :=
    MorphismProperty.of_isPullback (P := @IsAffineHom)
      (IsPullback.of_hasPullback (ArithmeticGeometry.Descent.CMVariety.FiniteCoefficientDiagram.Abelian.finiteCoefficientBaseMap R B ∅) f) hbase
  have hV : IsCompact (V : Set (D.obj i)) :=
    QuasiCompact.isCompact_preimage (f := τ.app i) _ U.isOpen hU
  have hVclosed : IsClosed ((c.π.app i ⁻¹ᵁ V : c.pt.Opens) : Set c.pt) := by
    change IsClosed ((c.π.app i ⁻¹ᵁ (τ.app i ⁻¹ᵁ U) : c.pt.Opens) : Set c.pt)
    rw [← Scheme.Hom.comp_preimage, ArithmeticGeometry.Descent.CMVariety.FiniteCoefficientFst.Abelian.finiteCoefficientFamilyCone_structure]
    exact hclosed
  obtain ⟨j, a, ha⟩ := quasiCompactOpen_eventually_closed D c
    (ArithmeticGeometry.Descent.CMVariety.FiniteCoefficientFst.Abelian.finiteCoefficientFamilyConeIsLimit R B f) i V hV hVclosed
  have he : D.map a ≫ τ.app i = τ.app j := by
    exact (τ.naturality a).trans (Category.comp_id (τ.app j))
  refine ⟨j.unop, ?_⟩
  change IsClosed (τ.app j ⁻¹ᵁ U : Set (D.obj j))
  rw [← he, Scheme.Hom.comp_preimage]
  exact ha

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ClopenFiniteCoefficientDescent
