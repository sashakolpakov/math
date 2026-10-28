import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.ConstantSectionsOn
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Geometric.Splitting
import OAI.AlgebraicGeometry.AbelianScheme.TorsionQuotient.EmbeddingParametersIs
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Finite.ConstantScheme

/-! # Constant Base Change -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.ConstantBaseChange.ConstantGroupModels

noncomputable section

section

/-! Constant finite groups as actual group schemes, and closed subgroup
embeddings constructed from geometrically distinct group-valued sections.
The group operations come from the represented locally constant functor. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

open OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.ConstantSectionsOn.ConstantSections

variable (S : Scheme) (G : Type) [Group G]

def representable : (AbelianModuli.HilbertConstruction.Constant.GroupMaps.constantGroupFunctor S G ⋙ forget GrpCat).RepresentableBy
    (AbelianModuli.HilbertConstruction.ConstantScheme.Iff.constantScheme S G) where
  homEquiv := AbelianModuli.HilbertConstruction.ConstantScheme.Iff.constantSchemePointsEquiv S G _
  homEquiv_comp a x := by
    apply LocallyConstant.ext
    intro t
    rfl

instance group : GrpObj (AbelianModuli.HilbertConstruction.ConstantScheme.Iff.constantScheme S G) :=
  GrpObj.ofRepresentableBy _ (AbelianModuli.HilbertConstruction.Constant.GroupMaps.constantGroupFunctor S G) (representable S G)

def pointIso : yonedaGrpObj (AbelianModuli.HilbertConstruction.ConstantScheme.Iff.constantScheme S G) ≅ AbelianModuli.HilbertConstruction.Constant.GroupMaps.constantGroupFunctor S G :=
  yonedaGrpObjIsoOfRepresentableBy _ (AbelianModuli.HilbertConstruction.Constant.GroupMaps.constantGroupFunctor S G) (representable S G)

def labels : G →* (AbelianModuli.ReferenceFamily.ConstantSectionsOn.ConstantSections.baseTest S ⟶ AbelianModuli.HilbertConstruction.ConstantScheme.Iff.constantScheme S G) :=
  ((pointIso S G).inv.app (.op (AbelianModuli.ReferenceFamily.ConstantSectionsOn.ConstantSections.baseTest S))).hom.comp
    (LocallyConstant.constMonoidHom (X := S) (Y := G))

theorem labels_eq_component (g : G) : labels S G g = AbelianModuli.ReferenceFamily.ConstantSectionsOn.ConstantSections.component S g := by
  apply (AbelianModuli.HilbertConstruction.ConstantScheme.Iff.constantSchemePointsEquiv S G (AbelianModuli.ReferenceFamily.ConstantSectionsOn.ConstantSections.baseTest S)).injective
  change (AbelianModuli.HilbertConstruction.ConstantScheme.Iff.constantSchemePointsEquiv S G (AbelianModuli.ReferenceFamily.ConstantSectionsOn.ConstantSections.baseTest S))
      ((AbelianModuli.HilbertConstruction.ConstantScheme.Iff.constantSchemePointsEquiv S G (AbelianModuli.ReferenceFamily.ConstantSectionsOn.ConstantSections.baseTest S)).symm (LocallyConstant.const S g)) = _
  rw [Equiv.apply_symm_apply]
  apply LocallyConstant.ext
  intro s
  exact (AbelianModuli.HilbertConstruction.ConstantScheme.Iff.constantSchemeIndex_ι g s).symm

theorem labels_injective [Nonempty S] : Function.Injective (labels S G) := by
  intro g h he
  have hi := congrArg (fun p : AbelianModuli.ReferenceFamily.ConstantSectionsOn.ConstantSections.baseTest S ⟶ AbelianModuli.HilbertConstruction.ConstantScheme.Iff.constantScheme S G =>
    AbelianModuli.HilbertConstruction.ConstantScheme.Iff.constantSchemeIndex S G (p.left (Classical.arbitrary S))) he
  rw [labels_eq_component, labels_eq_component] at hi
  change AbelianModuli.HilbertConstruction.ConstantScheme.Iff.constantSchemeIndex S G (Sigma.ι (fun _ : G => S) g (Classical.arbitrary S)) =
    AbelianModuli.HilbertConstruction.ConstantScheme.Iff.constantSchemeIndex S G (Sigma.ι (fun _ : G => S) h (Classical.arbitrary S)) at hi
  simpa only [AbelianModuli.HilbertConstruction.ConstantScheme.Iff.constantSchemeIndex_ι] using hi

variable {S G} {H : Over S} [GrpObj H]

def sectionsGroupMap (a : G →* (AbelianModuli.ReferenceFamily.ConstantSectionsOn.ConstantSections.baseTest S ⟶ H)) :
    Grp.mk (AbelianModuli.HilbertConstruction.ConstantScheme.Iff.constantScheme S G) ⟶ Grp.mk H :=
  yonedaGrpFullyFaithful.preimage ((pointIso S G).hom ≫ AbelianModuli.ReferenceFamily.ConstantSectionsOn.ConstantSections.extendNatTrans a)

theorem sectionsGroupMap_hom (a : G →* (AbelianModuli.ReferenceFamily.ConstantSectionsOn.ConstantSections.baseTest S ⟶ H)) :
    (sectionsGroupMap a).hom.hom = AbelianModuli.ReferenceFamily.ConstantSectionsOn.ConstantSections.sectionsMap (⇑a) := by
  let e := AbelianModuli.HilbertConstruction.ConstantScheme.Iff.constantSchemePointsEquiv S G (AbelianModuli.HilbertConstruction.ConstantScheme.Iff.constantScheme S G)
  change e.symm (e (𝟙 _)) ≫ AbelianModuli.ReferenceFamily.ConstantSectionsOn.ConstantSections.sectionsMap (⇑a) = AbelianModuli.ReferenceFamily.ConstantSectionsOn.ConstantSections.sectionsMap (⇑a)
  rw [e.symm_apply_apply, Category.id_comp]

instance sectionsMap_isMonHom (a : G →* (AbelianModuli.ReferenceFamily.ConstantSectionsOn.ConstantSections.baseTest S ⟶ H)) :
    IsMonHom (AbelianModuli.ReferenceFamily.ConstantSectionsOn.ConstantSections.sectionsMap (⇑a)) := by
  rw [← sectionsGroupMap_hom a]
  infer_instance

/-- Geometric distinctness of the labels proves monicity on every test
scheme, including disconnected and nonreduced schemes. -/
theorem sectionsMap_mono (a : G →* (AbelianModuli.ReferenceFamily.ConstantSectionsOn.ConstantSections.baseTest S ⟶ H))
    (ha : AbelianScheme.TorsionQuotient.EmbeddingParametersIs.EmbeddingParameters.Distinct H G a) : Mono (AbelianModuli.ReferenceFamily.ConstantSectionsOn.ConstantSections.sectionsMap (⇑a)) := by
  have hind (U : Over S) (hne : Nonempty U.left) (c : G)
      (hc : AbelianModuli.ReferenceFamily.ConstantSectionsOn.ConstantSections.toBase U ≫ a c = 1) : c = 1 := by
    let u := Classical.choice hne
    let k := U.left.residueField u
    let s := U.left.fromSpecResidueField u ≫ U.hom
    let p : Over.mk s ⟶ U := Over.homMk (U.left.fromSpecResidueField u) rfl
    apply ha k s (p ≫ AbelianModuli.ReferenceFamily.ConstantSectionsOn.ConstantSections.toBase U)
    change (p ≫ AbelianModuli.ReferenceFamily.ConstantSectionsOn.ConstantSections.toBase U) ≫ a c = (p ≫ AbelianModuli.ReferenceFamily.ConstantSectionsOn.ConstantSections.toBase U) ≫ a 1
    rw [Category.assoc, hc, a.map_one, MonObj.comp_one]
    exact (MonObj.comp_one (p ≫ AbelianModuli.ReferenceFamily.ConstantSectionsOn.ConstantSections.toBase U)).symm
  constructor
  intro T x y hxy
  apply (AbelianModuli.HilbertConstruction.ConstantScheme.Iff.constantSchemePointsEquiv S G T).injective
  apply AbelianModuli.ReferenceFamily.ConstantSectionsOn.ConstantSections.extendHom_injective a hind T
  change (AbelianModuli.HilbertConstruction.ConstantScheme.Iff.constantSchemePointsEquiv S G T).symm
      ((AbelianModuli.HilbertConstruction.ConstantScheme.Iff.constantSchemePointsEquiv S G T) x) ≫ AbelianModuli.ReferenceFamily.ConstantSectionsOn.ConstantSections.sectionsMap (⇑a) =
    (AbelianModuli.HilbertConstruction.ConstantScheme.Iff.constantSchemePointsEquiv S G T).symm
      ((AbelianModuli.HilbertConstruction.ConstantScheme.Iff.constantSchemePointsEquiv S G T) y) ≫ AbelianModuli.ReferenceFamily.ConstantSectionsOn.ConstantSections.sectionsMap (⇑a)
  rw [Equiv.symm_apply_apply, Equiv.symm_apply_apply]
  exact hxy

variable [Finite G] [IsFinite H.hom] [Etale H.hom]

/-- The finite constant group is embedded as an actual closed subgroup
scheme by the supplied geometrically distinct group-valued sections. -/
theorem constant_subgroup_closed
    (a : G →* (AbelianModuli.ReferenceFamily.ConstantSectionsOn.ConstantSections.baseTest S ⟶ H))
    (ha : AbelianScheme.TorsionQuotient.EmbeddingParametersIs.EmbeddingParameters.Distinct H G a) :
    IsClosedImmersion (AbelianModuli.ReferenceFamily.ConstantSectionsOn.ConstantSections.sectionsMap (⇑a)).left ∧
      IsFinite (AbelianModuli.HilbertConstruction.ConstantScheme.Iff.constantScheme S G).hom ∧ Etale (AbelianModuli.HilbertConstruction.ConstantScheme.Iff.constantScheme S G).hom ∧
      IsMonHom (AbelianModuli.ReferenceFamily.ConstantSectionsOn.ConstantSections.sectionsMap (⇑a)) ∧ ∀ g, AbelianModuli.ReferenceFamily.ConstantSectionsOn.ConstantSections.component S g ≫ AbelianModuli.ReferenceFamily.ConstantSectionsOn.ConstantSections.sectionsMap (⇑a) = a g := by
  have : Mono (AbelianModuli.ReferenceFamily.ConstantSectionsOn.ConstantSections.sectionsMap (⇑a)) := sectionsMap_mono a ha
  have hf : IsFinite (AbelianModuli.ReferenceFamily.ConstantSectionsOn.ConstantSections.sectionsMap (⇑a)).left :=
    (AbelianScheme.TorsionQuotient.FiniteEtaleLift.FiniteEtaleLimits.hom_finite_etale (AbelianModuli.ReferenceFamily.ConstantSectionsOn.ConstantSections.sectionsMap (⇑a))).1
  exact ⟨(IsClosedImmersion.iff_isFinite_and_mono _).mpr ⟨hf, inferInstance⟩,
    inferInstance, inferInstance, inferInstance, AbelianModuli.ReferenceFamily.ConstantSectionsOn.ConstantSections.component_sectionsMap (⇑a)⟩

variable {k : Type} [Field k] [IsSepClosed k]
  (H : Over (Spec (.of k))) [GrpObj H] [IsFinite H.hom] [Etale H.hom]

/-- A finite étale group scheme over an algebraically closed field has an
actual constant group-scheme model, with its group comparison constructed. -/
theorem exists_constant_group_model :
    ∃ (G : Type) (_ : Group G) (_ : Finite G),
      ∃ e : AbelianModuli.HilbertConstruction.ConstantScheme.Iff.constantScheme (Spec (.of k)) G ≅ H, IsMonHom e.hom := by
  obtain ⟨G, hG, hfin, ⟨e⟩⟩ := AbelianModuli.ReferenceFamily.Geometric.Splitting.GeometricSplitting.exists_constant_groupIso H
  let eG : Grp.mk (AbelianModuli.HilbertConstruction.ConstantScheme.Iff.constantScheme (Spec (.of k)) G) ≅ Grp.mk H :=
    yonedaGrpFullyFaithful.preimageIso (pointIso (Spec (.of k)) G ≪≫ e)
  let eS := (Grp.forget (Over (Spec (.of k)))).mapIso eG
  exact ⟨G, hG, hfin, eS, inferInstanceAs (IsMonHom eG.hom.hom.hom)⟩

end

/-! The canonical constant-scheme base-change isomorphism has the expected
map on every label. This supplies an actual cartesian square for the
arithmetic finite subgroup models, with no abstract comparison premise. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

open OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.ConstantSectionsOn.ConstantSections

variable {S S' : Scheme} (f : S' ⟶ S) (I : Type)

def scalarMap : (∐ fun _ : I => S') ⟶ (∐ fun _ : I => S) :=
  Sigma.desc (fun i => f ≫ Sigma.ι (fun _ : I => S) i)

@[reassoc] theorem component_scalarMap (i : I) :
    Sigma.ι (fun _ : I => S') i ≫ scalarMap f I = f ≫ Sigma.ι (fun _ : I => S) i :=
  Sigma.ι_comp_desc _ _

theorem scalarMap_base :
    scalarMap f I ≫ (AbelianModuli.HilbertConstruction.ConstantScheme.Iff.constantScheme S I).hom = (AbelianModuli.HilbertConstruction.ConstantScheme.Iff.constantScheme S' I).hom ≫ f := by
  change scalarMap f I ≫ Sigma.desc (fun _ : I => 𝟙 S) =
    Sigma.desc (fun _ : I => 𝟙 S') ≫ f
  apply Sigma.hom_ext
  intro i
  rw [component_scalarMap_assoc, Sigma.ι_comp_desc,
    Category.comp_id, Sigma.ι_comp_desc_assoc, Category.id_comp]

theorem baseChangeIso_fst :
    (AbelianModuli.HilbertConstruction.Constant.BaseChange.constantSchemeBaseChangeIso f I).hom.left ≫
      pullback.fst (AbelianModuli.HilbertConstruction.ConstantScheme.Iff.constantScheme S I).hom f = scalarMap f I := by
  apply Sigma.hom_ext
  intro i
  apply Eq.trans ?_ (component_scalarMap f I i).symm
  let e₀ := AbelianModuli.HilbertConstruction.Constant.BaseChange.constantSetRepresentable S' I
  let e₁ := AbelianModuli.HilbertConstruction.Constant.BaseChange.constantSetPullbackRepresentable f I
  let e := AbelianModuli.HilbertConstruction.Constant.BaseChange.constantSchemeBaseChangeIso f I
  have he : e₁.homEquiv e.hom = e₀.homEquiv (𝟙 _) :=
    e₁.homEquiv.apply_symm_apply _
  have hp : e₁.homEquiv (AbelianModuli.ReferenceFamily.ConstantSectionsOn.ConstantSections.component S' i ≫ e.hom) = LocallyConstant.const S' i := by
    rw [e₁.homEquiv_comp, he]
    apply LocallyConstant.ext
    intro s
    exact AbelianModuli.HilbertConstruction.ConstantScheme.Iff.constantSchemeIndex_ι i s
  let q : (Over.map f).obj (AbelianModuli.ReferenceFamily.ConstantSectionsOn.ConstantSections.baseTest S') ⟶ AbelianModuli.HilbertConstruction.ConstantScheme.Iff.constantScheme S I :=
    Over.homMk (f ≫ Sigma.ι (fun _ : I => S) i) (by
      change (f ≫ Sigma.ι (fun _ : I => S) i) ≫ Sigma.desc (fun _ : I => 𝟙 S) = 𝟙 S' ≫ f
      rw [Category.assoc, Sigma.ι_comp_desc, Category.comp_id, Category.id_comp])
  have hq : AbelianModuli.HilbertConstruction.ConstantScheme.Iff.constantSchemePointsEquiv S I ((Over.map f).obj (AbelianModuli.ReferenceFamily.ConstantSectionsOn.ConstantSections.baseTest S')) q =
      LocallyConstant.const S' i := by
    apply LocallyConstant.ext
    intro s
    exact AbelianModuli.HilbertConstruction.ConstantScheme.Iff.constantSchemeIndex_ι i (f s)
  have hm : ((Over.mapPullbackAdj f).homEquiv (AbelianModuli.ReferenceFamily.ConstantSectionsOn.ConstantSections.baseTest S') (AbelianModuli.HilbertConstruction.ConstantScheme.Iff.constantScheme S I)).symm
      (AbelianModuli.ReferenceFamily.ConstantSectionsOn.ConstantSections.component S' i ≫ e.hom) = q :=
    (AbelianModuli.HilbertConstruction.ConstantScheme.Iff.constantSchemePointsEquiv S I ((Over.map f).obj (AbelianModuli.ReferenceFamily.ConstantSectionsOn.ConstantSections.baseTest S'))).injective
      (hp.trans hq.symm)
  exact (Category.assoc _ _ _).symm.trans (congrArg Over.Hom.left hm)

/-- The scalar map on the actual disjoint unions is a base-change square. -/
theorem scalarMap_isPullback :
    IsPullback (scalarMap f I) (AbelianModuli.HilbertConstruction.ConstantScheme.Iff.constantScheme S' I).hom
      (AbelianModuli.HilbertConstruction.ConstantScheme.Iff.constantScheme S I).hom f :=
  IsPullback.of_iso_pullback ⟨scalarMap_base f I⟩
    ((Over.forget S').mapIso (AbelianModuli.HilbertConstruction.Constant.BaseChange.constantSchemeBaseChangeIso f I))
    (baseChangeIso_fst f I) (AbelianModuli.HilbertConstruction.Constant.BaseChange.constantSchemeBaseChangeIso f I).hom.w

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.ConstantBaseChange.ConstantGroupModels
