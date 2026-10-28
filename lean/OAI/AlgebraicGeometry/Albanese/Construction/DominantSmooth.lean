import OAI.AlgebraicGeometry.Albanese.Construction.DominantDimension

/-! # Dominant Smooth -/

namespace OAI.AlgebraicGeometry.Albanese.Construction.DominantSmooth

noncomputable section

open _root_.CategoryTheory _root_.AlgebraicGeometry

/-- In characteristic zero, a dominant finite-type morphism of integral
varieties is smooth at the generic point of its source. -/
theorem dominant_genericPoint_mem_smoothLocus
    {X Y : Scheme} [IsIntegral X] [IsIntegral Y]
    (i : X ⟶ Y) [IsDominant i] [LocallyOfFinitePresentation i]
    (f : Y ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) : genericPoint X ∈ i.smoothLocus := by
  have hpoint := DominantDimension.dominant_genericPoint i
  have hchar : CharZero Y.functionField :=
    charZero_of_injective_ringHom (Foundations.Scheme.FunctionFieldScalar.functionFieldScalarMap f).injective
  have hfield : IsField (Y.presheaf.stalk (i (genericPoint X))) := by
    rw [hpoint]
    exact Field.toIsField Y.functionField
  have : CharZero (Y.presheaf.stalk (i (genericPoint X))) := by
    rw [hpoint]
    exact hchar
  let _ := hfield.toField
  have := LocallyOfFiniteType.stalkMap i (genericPoint X)
  rw [Scheme.Hom.mem_smoothLocus]
  algebraize [(i.stalkMap (genericPoint X)).hom]
  exact Algebra.FormallySmooth.of_perfectField

/-- Dominance in characteristic zero supplies a dense smooth locus. -/
theorem dominant_dense_smoothLocus
    {X Y : Scheme} [IsIntegral X] [IsIntegral Y]
    (i : X ⟶ Y) [IsDominant i] [LocallyOfFinitePresentation i]
    (f : Y ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) : Dense (i.smoothLocus : Set X) := by
  apply dense_iff_closure_eq.mpr
  apply Set.eq_univ_of_univ_subset
  rw [← genericPoint_spec X]
  exact closure_mono (Set.singleton_subset_iff.mpr
    (dominant_genericPoint_mem_smoothLocus i f))

set_option backward.isDefEq.respectTransparency false in
/-- Postcomposition with an isomorphism preserves the smooth locus. -/
theorem smoothLocus_comp_isIso {X Y Z : Scheme} (f : X ⟶ Y) (g : Y ⟶ Z)
    [LocallyOfFinitePresentation f] [IsIso g] : (f ≫ g).smoothLocus = f.smoothLocus := by
  ext x
  change ((f ≫ g).stalkMap x).hom.FormallySmooth ↔ (f.stalkMap x).hom.FormallySmooth
  rw [Scheme.Hom.stalkMap_comp]
  exact RingHom.FormallySmooth.respectsIso.cancel_left_isIso (g.stalkMap (f x)) (f.stalkMap x)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- A nonempty smooth locus extends to every point when algebraic
automorphisms act transitively on the source and commute with the morphism. -/
theorem smooth_of_point_equivariant (X Y : Over Foundations.Scheme.ProjectiveSpace.complexBase)
    [LocallyOfFiniteType X.hom] (f : X ⟶ Y) [LocallyOfFinitePresentation f.left]
    (hsmooth : (f.left.smoothLocus : Set X.left).Nonempty)
    (htrans : ∀ p q : Over.mk (𝟙 Foundations.Scheme.ProjectiveSpace.complexBase) ⟶ X,
      ∃ (e : X ≅ X) (d : Y ≅ Y), p ≫ e.hom = q ∧ e.hom ≫ f = f ≫ d.hom) :
    Smooth f.left := by
  have : JacobsonSpace X.left := LocallyOfFiniteType.jacobsonSpace X.hom
  rw [← Scheme.Hom.smoothLocus_eq_top_iff, ← TopologicalSpace.Opens.coe_eq_univ,
    ← not_ne_iff, ← Set.nonempty_compl]
  intro hbad
  obtain ⟨x, hx, hxc⟩ := nonempty_inter_closedPoints hbad
    f.left.smoothLocus.2.isClosed_compl.isLocallyClosed
  obtain ⟨y, hy, hyc⟩ := nonempty_inter_closedPoints hsmooth
    f.left.smoothLocus.2.isLocallyClosed
  let p : Over.mk (𝟙 Foundations.Scheme.ProjectiveSpace.complexBase) ⟶ X :=
    Over.homMk _ ((pointEquivClosedPoint X.hom).symm ⟨x, hxc⟩).2
  let q : Over.mk (𝟙 Foundations.Scheme.ProjectiveSpace.complexBase) ⟶ X :=
    Over.homMk _ ((pointEquivClosedPoint X.hom).symm ⟨y, hyc⟩).2
  obtain ⟨e, d, he, hcomm⟩ := htrans p q
  have hexy : e.hom.left x = y := by
    simpa [p, q, pointEquivClosedPoint] using congr(($he).left (IsLocalRing.closedPoint ℂ))
  have : IsIso e.hom.left := (Over.forget _).map_isIso e.hom
  have : IsIso d.hom.left := (Over.forget _).map_isIso d.hom
  have hxpre : x ∈ e.hom.left ⁻¹ᵁ f.left.smoothLocus := by
    change e.hom.left x ∈ f.left.smoothLocus
    rw [hexy]
    exact hy
  have hcomm' : e.hom.left ≫ f.left = f.left ≫ d.hom.left := congrArg Over.Hom.left hcomm
  rw! [Scheme.Hom.preimage_smoothLocus_eq, hcomm', smoothLocus_comp_isIso] at hxpre
  exact hx hxpre

open MonoidalCategory CartesianMonoidalCategory MonObj

/-- Group homomorphisms intertwine translation by a point with translation
by its image. -/
theorem mulRight_hom_comp (G H : Over Foundations.Scheme.ProjectiveSpace.complexBase) [GrpObj G] [GrpObj H]
    (f : G ⟶ H) [IsMonHom f] (z : Over.mk (𝟙 Foundations.Scheme.ProjectiveSpace.complexBase) ⟶ G) :
    (GrpObj.mulRight z).hom ≫ f = f ≫ (GrpObj.mulRight (z ≫ f)).hom := by
  change (𝟙 G * (toUnit G ≫ z)) ≫ f = f ≫ (𝟙 H * (toUnit H ≫ z ≫ f))
  rw [MonObj.mul_comp, MonObj.comp_mul]
  simp [Category.assoc]

/-- A dominant homomorphism of complex abelian varieties is smooth at every
point. Generic smoothness and translation equivariance supply the proof. -/
theorem dominant_abelian_hom_smooth (A B : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety)
    (f : A.toOver ⟶ B.toOver) [IsMonHom f] [IsDominant f.left] : Smooth f.left := by
  have : IsIntegral A.toOver.left := inferInstanceAs (IsIntegral A.carrier)
  have : IsIntegral B.toOver.left := inferInstanceAs (IsIntegral B.carrier)
  have : LocallyOfFiniteType A.toOver.hom :=
    inferInstanceAs (LocallyOfFiniteType A.variety.structureMap)
  have : LocallyOfFiniteType B.toOver.hom :=
    inferInstanceAs (LocallyOfFiniteType B.variety.structureMap)
  have : IsLocallyNoetherian B.toOver.left :=
    LocallyOfFiniteType.isLocallyNoetherian B.toOver.hom
  have : LocallyOfFiniteType (f.left ≫ B.toOver.hom) := by rw [f.w]; infer_instance
  have : LocallyOfFiniteType f.left := locallyOfFiniteType_of_comp f.left B.toOver.hom
  apply smooth_of_point_equivariant A.toOver B.toOver f
    (dominant_dense_smoothLocus f.left B.toOver.hom).nonempty
  intro p q
  let z := p⁻¹ * q
  refine ⟨GrpObj.mulRight z, GrpObj.mulRight (z ≫ f), ?_, mulRight_hom_comp _ _ f z⟩
  rw [SubgroupScheme.point_mulRight]
  simp [z]

/-- Homomorphic refinements of generated targets are smooth surjections. -/
theorem refinement_smooth (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation)
    (A B : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) (a : X.toOver ⟶ A.toOver) (b : X.toOver ⟶ B.toOver)
    (φ : A.toOver ⟶ B.toOver) [IsMonHom φ] (hφ : a ≫ φ = b)
    (hb : GeneratedClosed.Generates X B b) : Smooth φ.left := by
  have : Surjective φ.left := GeneratedClosed.refinement_surjective X A B a b φ hφ hb
  have : IsDominant φ.left := ⟨φ.left.surjective.denseRange⟩
  exact dominant_abelian_hom_smooth A B φ

end

end OAI.AlgebraicGeometry.Albanese.Construction.DominantSmooth
