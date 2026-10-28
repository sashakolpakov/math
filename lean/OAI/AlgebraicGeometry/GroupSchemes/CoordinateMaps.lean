import OAI.AlgebraicGeometry.GroupSchemes.AffineHopf

/-! # Coordinate Maps -/

namespace OAI.AlgebraicGeometry.GroupSchemes

noncomputable section

/-! Coordinate morphisms recovered from the given geometric morphisms. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.MonObj

universe u
variable {k : Type u} [Field k]

/-- Pullback on coordinate algebras under the actual affine scheme morphism. -/
def FiniteEtale.FiniteCommGroupScheme.coordinateMap {G H : FiniteEtale.FiniteCommGroupScheme k} (f : G.scheme ⟶ H.scheme) :
    H.algebra →ₐ[k] G.algebra :=
  ((algSpec.fullyFaithful (R := CommRingCat.of k)).preimage f).unop.hom

/-- Spec of the recovered algebra map is the original scheme map. -/
theorem FiniteEtale.FiniteCommGroupScheme.coordinateMap_spec {G H : FiniteEtale.FiniteCommGroupScheme k} (f : G.scheme ⟶ H.scheme) :
    (algSpec (CommRingCat.of k)).map (CommAlgCat.ofHom (FiniteEtale.FiniteCommGroupScheme.coordinateMap f)).op = f :=
  (algSpec.fullyFaithful (R := CommRingCat.of k)).map_preimage f

theorem FiniteEtale.FiniteCommGroupScheme.coordinateMap_id (G : FiniteEtale.FiniteCommGroupScheme k) :
    FiniteEtale.FiniteCommGroupScheme.coordinateMap (𝟙 G.scheme) = AlgHom.id k G.algebra := by
  exact congrArg (fun f : op G.algebra ⟶ op G.algebra => f.unop.hom)
    (algSpec.fullyFaithful (R := CommRingCat.of k)).preimage_id

theorem FiniteEtale.FiniteCommGroupScheme.coordinateMap_comp {G H J : FiniteEtale.FiniteCommGroupScheme k}
    (f : G.scheme ⟶ H.scheme) (g : H.scheme ⟶ J.scheme) :
    FiniteEtale.FiniteCommGroupScheme.coordinateMap (f ≫ g) = (FiniteEtale.FiniteCommGroupScheme.coordinateMap f).comp (FiniteEtale.FiniteCommGroupScheme.coordinateMap g) := by
  exact congrArg (fun f : op G.algebra ⟶ op J.algebra => f.unop.hom)
    ((algSpec.fullyFaithful (R := CommRingCat.of k)).preimage_comp f g)

/-- Pullback preserves the group laws reconstructed on the coordinate algebras. -/
theorem FiniteEtale.FiniteCommGroupScheme.coordinateMap_isMonHom {G H : FiniteEtale.FiniteCommGroupScheme k}
    (f : G.scheme ⟶ H.scheme) [IsMonHom f] :
    letI := G.coordinateGroup
    letI := H.coordinateGroup
    IsMonHom (CommAlgCat.ofHom (FiniteEtale.FiniteCommGroupScheme.coordinateMap f)).op := by
  let : (algSpec (CommRingCat.of k)).Braided := braidedAlgSpec
  let := G.coordinateGroup
  let := H.coordinateGroup
  constructor
  · apply (algSpec.fullyFaithful (R := CommRingCat.of k)).map_injective
    change (algSpec (CommRingCat.of k)).map
      ((algSpec.fullyFaithful (R := CommRingCat.of k)).preimage
        (Functor.OplaxMonoidal.η (algSpec (CommRingCat.of k)) ≫ η[G.scheme]) ≫
        (algSpec.fullyFaithful (R := CommRingCat.of k)).preimage f) = _
    simp only [Functor.map_comp, Functor.FullyFaithful.map_preimage]
    rw [Category.assoc, IsMonHom.one_hom]
    exact ((algSpec.fullyFaithful (R := CommRingCat.of k)).map_preimage _).symm
  · apply (algSpec.fullyFaithful (R := CommRingCat.of k)).map_injective
    change (algSpec (CommRingCat.of k)).map
      ((algSpec.fullyFaithful (R := CommRingCat.of k)).preimage
        (Functor.OplaxMonoidal.δ (algSpec (CommRingCat.of k)) _ _ ≫ μ[G.scheme]) ≫
        (algSpec.fullyFaithful (R := CommRingCat.of k)).preimage f) = _
    simp only [Functor.map_comp, Functor.FullyFaithful.map_preimage]
    rw [Category.assoc, IsMonHom.mul_hom]
    change _ = (algSpec (CommRingCat.of k)).map
      ((CommAlgCat.ofHom (FiniteEtale.FiniteCommGroupScheme.coordinateMap f)).op ⊗ₘ
        (CommAlgCat.ofHom (FiniteEtale.FiniteCommGroupScheme.coordinateMap f)).op) ≫
      (algSpec (CommRingCat.of k)).map
        ((algSpec.fullyFaithful (R := CommRingCat.of k)).preimage
          (Functor.OplaxMonoidal.δ (algSpec (CommRingCat.of k)) _ _ ≫ μ[H.scheme]))
    rw [Functor.FullyFaithful.map_preimage,
      ← Functor.OplaxMonoidal.δ_natural_assoc, FiniteEtale.FiniteCommGroupScheme.coordinateMap_spec]
    rfl

/-- Pullback along a group-scheme morphism is a genuine bialgebra map. -/
def FiniteEtale.FiniteCommGroupScheme.coordinateBialgMap {G H : FiniteEtale.FiniteCommGroupScheme k}
    (f : G.scheme ⟶ H.scheme) [IsMonHom f] :
    letI := G.coordinateHopf
    letI := H.coordinateHopf
    letI := G.coordinateCoalgebra
    letI := H.coordinateCoalgebra
    H.algebra →ₐc[k] G.algebra := by
  let := G.coordinateGroup
  let := H.coordinateGroup
  have := FiniteEtale.FiniteCommGroupScheme.coordinateMap_isMonHom f
  let g : Grp.mk (op G.algebra) ⟶ Grp.mk (op H.algebra) :=
    Grp.homMk (CommAlgCat.ofHom (FiniteEtale.FiniteCommGroupScheme.coordinateMap f)).op
  exact ((commHopfAlgCatEquivCogrpCommAlgCat k).inverse.map
    g.op).hom

/-- The bialgebra map has exactly the original affine pullback as underlying map. -/
theorem FiniteEtale.FiniteCommGroupScheme.coordinateBialgMap_toAlgHom {G H : FiniteEtale.FiniteCommGroupScheme k}
    (f : G.scheme ⟶ H.scheme) [IsMonHom f] :
    letI := G.coordinateHopf
    letI := H.coordinateHopf
    letI := G.coordinateCoalgebra
    letI := H.coordinateCoalgebra
    (FiniteEtale.FiniteCommGroupScheme.coordinateBialgMap f).toAlgHom = FiniteEtale.FiniteCommGroupScheme.coordinateMap f := rfl

/-- A geometric closed immersion gives a surjection on the recovered coordinate algebras. -/
theorem FiniteEtale.FiniteCommGroupScheme.coordinateMap_surjective {G H : FiniteEtale.FiniteCommGroupScheme k}
    (f : G.scheme ⟶ H.scheme) [IsClosedImmersion f.left] :
    Function.Surjective (FiniteEtale.FiniteCommGroupScheme.coordinateMap f) := by
  let q := CommRingCat.ofHom (FiniteEtale.FiniteCommGroupScheme.coordinateMap f).toRingHom
  have hs : Spec.map q = f.left := congrArg Over.Hom.left (FiniteEtale.FiniteCommGroupScheme.coordinateMap_spec f)
  have hf : IsClosedImmersion f.left := inferInstance
  have : IsClosedImmersion (Spec.map q) := hs.symm ▸ hf
  have hsurj := (IsClosedImmersion.isAffine_surjective_of_isAffine (Spec.map q)).2
  have he : (Scheme.ΓSpecIso (CommRingCat.of H.algebra)).inv ≫
      (Spec.map q).appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of G.algebra)).hom = q := by
    rw [Scheme.ΓSpecIso_naturality, Iso.inv_hom_id_assoc]
  have h := (ConcreteCategory.bijective_of_isIso
    (Scheme.ΓSpecIso (CommRingCat.of G.algebra)).hom).2.comp
      (hsurj.comp (ConcreteCategory.bijective_of_isIso
        (Scheme.ΓSpecIso (CommRingCat.of H.algebra)).inv).2)
  change Function.Surjective ((Scheme.ΓSpecIso (CommRingCat.of H.algebra)).inv ≫
    (Spec.map q).appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of G.algebra)).hom) at h
  change Function.Surjective q
  simpa only [he] using h

end

end OAI.AlgebraicGeometry.GroupSchemes
