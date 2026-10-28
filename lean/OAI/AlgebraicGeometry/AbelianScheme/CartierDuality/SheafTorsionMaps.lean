import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.RelativeCoprimeTorsion

/-! # Sheaf Torsion Maps -/

namespace OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.SheafTorsionMaps

noncomputable section

/-!
# CartierDuality: canonical maps of actual torsion fppf sheaves
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

universe u

namespace Construction.Schemes

/-- Every homomorphism of commutative fppf sheaves commutes with powers. -/
theorem sheafPower_naturality {S : Scheme.{u}} {F G : CommutativeSheavesAb.Construction.Schemes.FppfAb S} (f : F ⟶ G) (n : ℕ) :
    TorsionSheaves.Construction.Schemes.sheafPower F n ≫ f = f ≫ TorsionSheaves.Construction.Schemes.sheafPower G n := by
  apply (sheafToPresheaf (Scheme.fppfTopology.over S) CommGrpCat.{u + 1}).map_injective
  apply NatTrans.ext
  funext T
  apply CommGrpCat.hom_ext
  apply MonoidHom.ext
  intro x
  exact (f.hom.app T).hom.map_pow x n

/-- The induced map is the canonical map of the categorical torsion kernels. -/
def torsionSheafMap {S : Scheme.{u}} {F G : CommutativeSheavesAb.Construction.Schemes.FppfAb S} (f : F ⟶ G) (n : ℕ) :
    TorsionSheaves.Construction.Schemes.torsionFppfAb F n ⟶ TorsionSheaves.Construction.Schemes.torsionFppfAb G n :=
  kernel.map (TorsionSheaves.Construction.Schemes.sheafPower F n) (TorsionSheaves.Construction.Schemes.sheafPower G n) f f (sheafPower_naturality f n)

theorem torsionSheafMap_inclusion {S : Scheme.{u}} {F G : CommutativeSheavesAb.Construction.Schemes.FppfAb S} (f : F ⟶ G) (n : ℕ) :
    torsionSheafMap f n ≫ kernel.ι (TorsionSheaves.Construction.Schemes.sheafPower G n) = kernel.ι (TorsionSheaves.Construction.Schemes.sheafPower F n) ≫ f :=
  kernel.lift_ι _ _ _

/-- The native representation identifies the actual subgroup inclusions. -/
theorem nativeTorsionSheafIso_inclusion {S : Scheme.{u}} (G : Grp (Over S))
    [IsCommMonObj G.X] (n : ℕ) :
    (TorsionSheaves.Construction.Schemes.nativeTorsionSheafIso G n).hom ≫ kernel.ι (TorsionSheaves.Construction.Schemes.sheafPower (CommutativeSheavesAb.Construction.Schemes.representedFppfAb S G) n) =
      RepresentedMorphisms.Construction.Schemes.representedFppfAbMap (TorsionSheaves.Construction.Schemes.nativeTorsionInclusion G n) :=
  (TorsionSheaves.Construction.Schemes.nativeTorsionSheafIsKernel G n).conePointUniqueUpToIso_hom_comp
    (limit.isLimit (parallelPair (TorsionSheaves.Construction.Schemes.sheafPower (CommutativeSheavesAb.Construction.Schemes.representedFppfAb S G) n) 0))
    WalkingParallelPair.zero

/-- The canonical native torsion map preserves the inherited group law. -/
theorem nativeTorsionMap_isMonHom {S : Scheme.{u}} {G H : Grp (Over S)}
    [IsCommMonObj G.X] [IsCommMonObj H.X] (f : G ⟶ H) (n : ℕ) :
    IsMonHom (CoprimeTorsionIs.Construction.CoprimeTorsion.torsionMap f.hom.hom n) := by
  have : Mono (TorsionQuotient.SubgroupFunctor.torsionι H.X n) :=
    inferInstanceAs (Mono (equalizer.ι ((𝟙 H.X) ^ n) (1 : H.X ⟶ H.X)))
  have : IsMonHom (TorsionQuotient.SubgroupFunctor.torsionι H.X n) := TorsionQuotient.Group.TorsionGroup.inclusion_isMonHom H.X n
  have : IsMonHom (TorsionQuotient.SubgroupFunctor.torsionι G.X n) := TorsionQuotient.Group.TorsionGroup.inclusion_isMonHom G.X n
  have : IsMonHom (CoprimeTorsionIs.Construction.CoprimeTorsion.torsionMap f.hom.hom n ≫ TorsionQuotient.SubgroupFunctor.torsionι H.X n) := by
    rw [CoprimeTorsionIs.Construction.CoprimeTorsion.torsionMap_inclusion]
    infer_instance
  exact Picard.PoincareBundle.Kernel.Splitting.isMonHom_of_mono_postcomp _ (TorsionQuotient.SubgroupFunctor.torsionι H.X n)

/-- The canonical torsion morphism bundled as a native group morphism. -/
def nativeTorsionGroupMap {S : Scheme.{u}} {G H : Grp (Over S)}
    [IsCommMonObj G.X] [IsCommMonObj H.X] (f : G ⟶ H) (n : ℕ) :
    TorsionSheaves.Construction.Schemes.nativeTorsionGroup G n ⟶ TorsionSheaves.Construction.Schemes.nativeTorsionGroup H n :=
  @Grp.homMk (Over S) _ _ (TorsionSheaves.Construction.Schemes.nativeTorsionGroup G n) (TorsionSheaves.Construction.Schemes.nativeTorsionGroup H n)
    (CoprimeTorsionIs.Construction.CoprimeTorsion.torsionMap f.hom.hom n) (nativeTorsionMap_isMonHom f n)

theorem nativeTorsionGroupMap_inclusion {S : Scheme.{u}} {G H : Grp (Over S)}
    [IsCommMonObj G.X] [IsCommMonObj H.X] (f : G ⟶ H) (n : ℕ) :
    nativeTorsionGroupMap f n ≫ TorsionSheaves.Construction.Schemes.nativeTorsionInclusion H n = TorsionSheaves.Construction.Schemes.nativeTorsionInclusion G n ≫ f := by
  apply Grp.hom_ext
  exact CoprimeTorsionIs.Construction.CoprimeTorsion.torsionMap_inclusion f.hom.hom n

/-- Maps characterized by their inclusions respect any comparison of kernels. -/
theorem inclusion_comparison_natural {C : Type*} [Category C]
    {A B K L X Y : C} (a : A ⟶ K) (b : B ⟶ L) (k : K ⟶ X) (l : L ⟶ Y) [Mono l]
    (j : A ⟶ X) (j' : B ⟶ Y) (f : X ⟶ Y) (v : K ⟶ L) (u : A ⟶ B)
    (ha : a ≫ k = j) (hb : b ≫ l = j') (hv : v ≫ l = k ≫ f)
    (hu : u ≫ j' = j ≫ f) : u ≫ b = a ≫ v := by
  apply (cancel_mono l).mp
  rw [Category.assoc, hb, hu, Category.assoc, hv, ← Category.assoc, ha]

/-- The represented native torsion map agrees with the actual sheaf kernel map. -/
theorem nativeTorsionSheafIso_natural {S : Scheme.{u}} {G H : Grp (Over S)}
    [IsCommMonObj G.X] [IsCommMonObj H.X] (f : G ⟶ H) (n : ℕ) :
    RepresentedMorphisms.Construction.Schemes.representedFppfAbMap (nativeTorsionGroupMap f n) ≫ (TorsionSheaves.Construction.Schemes.nativeTorsionSheafIso H n).hom =
      (TorsionSheaves.Construction.Schemes.nativeTorsionSheafIso G n).hom ≫ torsionSheafMap (RepresentedMorphisms.Construction.Schemes.representedFppfAbMap f) n := by
  have hm : Mono (kernel.ι (TorsionSheaves.Construction.Schemes.sheafPower (CommutativeSheavesAb.Construction.Schemes.representedFppfAb S H) n)) :=
    inferInstanceAs (Mono (equalizer.ι (TorsionSheaves.Construction.Schemes.sheafPower (CommutativeSheavesAb.Construction.Schemes.representedFppfAb S H) n) 0))
  apply @inclusion_comparison_natural (CommutativeSheavesAb.Construction.Schemes.FppfAb S) inferInstance _ _ _ _ _ _
    (TorsionSheaves.Construction.Schemes.nativeTorsionSheafIso G n).hom
    (TorsionSheaves.Construction.Schemes.nativeTorsionSheafIso H n).hom
    (kernel.ι (TorsionSheaves.Construction.Schemes.sheafPower (CommutativeSheavesAb.Construction.Schemes.representedFppfAb S G) n))
    (kernel.ι (TorsionSheaves.Construction.Schemes.sheafPower (CommutativeSheavesAb.Construction.Schemes.representedFppfAb S H) n)) hm
    (RepresentedMorphisms.Construction.Schemes.representedFppfAbMap (TorsionSheaves.Construction.Schemes.nativeTorsionInclusion G n))
    (RepresentedMorphisms.Construction.Schemes.representedFppfAbMap (TorsionSheaves.Construction.Schemes.nativeTorsionInclusion H n)) (RepresentedMorphisms.Construction.Schemes.representedFppfAbMap f)
    _ _ (nativeTorsionSheafIso_inclusion G n) (nativeTorsionSheafIso_inclusion H n)
    (torsionSheafMap_inclusion (RepresentedMorphisms.Construction.Schemes.representedFppfAbMap f) n)
  exact (RepresentedMorphisms.Construction.Schemes.representedFppfAbMap_comp (nativeTorsionGroupMap f n) (TorsionSheaves.Construction.Schemes.nativeTorsionInclusion H n)).symm.trans
    ((congrArg (fun q => RepresentedMorphisms.Construction.Schemes.representedFppfAbMap q) (nativeTorsionGroupMap_inclusion f n)).trans
      (RepresentedMorphisms.Construction.Schemes.representedFppfAbMap_comp (TorsionSheaves.Construction.Schemes.nativeTorsionInclusion G n) f))

/-- Native isomorphisms of torsion induce isomorphisms of the actual
categorical kernels, through the canonical representation comparisons. -/
theorem torsionSheafMap_isIso_of_native {S : Scheme.{u}} {G H : Grp (Over S)}
    [IsCommMonObj G.X] [IsCommMonObj H.X] (f : G ⟶ H) (n : ℕ)
    [IsIso (CoprimeTorsionIs.Construction.CoprimeTorsion.torsionMap f.hom.hom n)] :
    IsIso (torsionSheafMap (RepresentedMorphisms.Construction.Schemes.representedFppfAbMap f) n) := by
  have : IsMonHom (CoprimeTorsionIs.Construction.CoprimeTorsion.torsionMap f.hom.hom n) := nativeTorsionMap_isMonHom f n
  let e : TorsionSheaves.Construction.Schemes.nativeTorsionGroup G n ≅ TorsionSheaves.Construction.Schemes.nativeTorsionGroup H n :=
    Grp.mkIso' (asIso (CoprimeTorsionIs.Construction.CoprimeTorsion.torsionMap f.hom.hom n))
  have he : RepresentedMorphisms.Construction.Schemes.representedFppfAbMap (nativeTorsionGroupMap f n) = (SheafBaseChange.Construction.Schemes.representedFppfAbIso e).hom := rfl
  have h : torsionSheafMap (RepresentedMorphisms.Construction.Schemes.representedFppfAbMap f) n =
      (TorsionSheaves.Construction.Schemes.nativeTorsionSheafIso G n).inv ≫ (SheafBaseChange.Construction.Schemes.representedFppfAbIso e).hom ≫
        (TorsionSheaves.Construction.Schemes.nativeTorsionSheafIso H n).hom := by
    rw [← he, nativeTorsionSheafIso_natural, Iso.inv_hom_id_assoc]
  rw [h]
  infer_instance

/-- Fiberwise coprime degree gives an isomorphism of the actual abelian
torsion fppf sheaves, with no invertibility condition on n. -/
theorem abelian_torsionSheafMap_isIso
    {S : Scheme.{u}} {g : ℕ} (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S)
    (D : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData A)
    (ell : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.Isogeny A D.abelian)
    (n : ℕ) (hn : 0 < n)
    (hdegree : ∀ s : S, n.Coprime (ell.hom.left.finrank (η[D.abelian.scheme].left s))) :
    IsIso (torsionSheafMap (RepresentedMorphisms.Construction.Schemes.representedFppfAbMap
      (@Grp.homMk (Over S) _ _ (Grp.mk A.scheme) (Grp.mk D.abelian.scheme)
        ell.hom ell.preservesGroup)) n) := by
  let f : Grp.mk A.scheme ⟶ Grp.mk D.abelian.scheme :=
    @Grp.homMk (Over S) _ _ (Grp.mk A.scheme) (Grp.mk D.abelian.scheme) ell.hom ell.preservesGroup
  have : IsIso (CoprimeTorsionIs.Construction.CoprimeTorsion.torsionMap f.hom.hom n) :=
    RelativeCoprimeTorsion.Construction.CoprimeTorsion.abelian_torsionMap_isIso A D ell n hn hdegree
  exact torsionSheafMap_isIso_of_native f n

end Construction.Schemes

end

end OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.SheafTorsionMaps
