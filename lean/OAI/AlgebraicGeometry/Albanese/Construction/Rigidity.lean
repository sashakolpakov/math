import OAI.AlgebraicGeometry.ComplexMultiplication.CMAbelianVariety

/-! # Rigidity -/

namespace OAI.AlgebraicGeometry.Albanese.Construction.Rigidity

noncomputable section

/-!
Rigidity tools for Construction. The geometric argument adapts the proof of
`AlgebraicGeometry.isCommMonObj_of_isProper_of_isIntegral_tensorObj_of_isAlgClosed`
in Mathlib/AlgebraicGeometry/Group/Abelian.lean (Andrew Yang and Christian Merten,
Apache 2.0). It applies the same finite-image argument to an arbitrary morphism
which is constant on the two identity axes.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open MonoidalCategory CartesianMonoidalCategory MonObj

universe u

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- A morphism from a proper integral group product, constant on both identity
axes, is constant everywhere. -/
theorem rigidity_eq_one {K : Type u} [Field K] [IsAlgClosed K]
    (G H : Over (Spec (.of K))) [IsProper G.hom] [IsProper H.hom]
    [IsIntegral (G ⊗ G).left] [GrpObj G] [GrpObj H]
    (d : G ⊗ G ⟶ H)
    (hl : η[G] ▷ G ≫ d = 1)
    (hr : G ◁ η[G] ≫ d = 1) : d = 1 := by
  let S := Spec (.of K)
  let point : S := IsLocalRing.closedPoint K
  have hpoint : IsClosed {point} := isClosed_discrete _
  have : Nonempty G.left := ⟨η[G].left point⟩
  have : IsProper (G ⊗ G).hom := by dsimp; infer_instance
  have : JacobsonSpace (G ⊗ G).left :=
    LocallyOfFiniteType.jacobsonSpace (Y := Spec _) (G ⊗ G).hom
  have : Surjective G.hom :=
    ⟨Function.surjective_to_subsingleton (α := G.left) (β := Spec _) _⟩
  have : IsProper (fst G G).left := by dsimp; infer_instance
  have : IsProper (fst G H).left := by dsimp; infer_instance
  have : Surjective (fst G G).left := by dsimp; infer_instance
  have : IsProper (d.left ≫ H.hom) := by rw [Over.w]; infer_instance
  have : IsClosedImmersion ((lift η[G] η[H]).left ≫ (fst G H).left) := by
    simpa using inferInstanceAs (IsClosedImmersion η[G].left)
  have : IsClosedImmersion (lift η[G] η[H]).left :=
    .of_comp _ (g := (fst G H).left)
  let γ : G ⊗ G ⟶ G ⊗ H := lift (fst _ _) d
  have : IsProper (γ.left ≫ (fst G H).left) := by simpa [γ]
  have : IsProper γ.left := .of_comp _ (fst G H).left
  have γ_right : (ρ_ G).inv ≫ G ◁ η[G] ≫ γ =
      (ρ_ G).inv ≫ G ◁ η[H] := by
    ext <;> simp [γ, hr, Hom.one_def]
  ext1
  have hfinite : γ.left '' ((fst G G).left ⁻¹' {η[G].left point}) ⊆
      {(lift η[G] η[H]).left point} := by
    rw [Set.image_subset_iff, ← Set.sdiff_eq_empty, ← Set.not_nonempty_iff_eq_empty]
    intro hne
    obtain ⟨c₀, ⟨hc₁, hc₂⟩, hc₃⟩ := nonempty_inter_closedPoints hne <| by
      rw [Set.sdiff_eq_compl_inter, ← Set.image_singleton, ← Set.image_singleton]
      refine (IsOpen.isLocallyClosed ?_).inter (IsClosed.isLocallyClosed ?_)
      · exact (((lift η[G] η[H]).left.isClosedMap _ hpoint).preimage
          γ.left.continuous).isOpen_compl
      · exact (η[G].left.isClosedMap _ hpoint).preimage (fst G G).left.continuous
    obtain ⟨⟨c, hc⟩, e⟩ := (pointEquivClosedPoint (G ⊗ G).hom).surjective ⟨c₀, hc₃⟩
    obtain rfl : c point = c₀ := congr(($e).1)
    let fc : 𝟙_ (Over S) ⟶ 𝟙_ (Over S) ⊗ G :=
      lift (𝟙 _) (Over.homMk c hc ≫ snd G G)
    have hcfirst : c ≫ pullback.fst G.hom G.hom = η[G].left :=
      ext_of_apply_closedPoint_eq G.hom (by simpa) (by simp) (by simpa)
    have hcdecomp : c = fc.left ≫ (η[G] ▷ G).left := by
      dsimp
      ext <;> simp [fc, S, hcfirst]
    have hcimage : fc ≫ η[G] ▷ G ≫ γ = lift η[G] η[H] := by
      ext1 <;> simp [fc, γ, S, hl, ← one_eq_one]
    exact hc₂ <| by
      simp [hcdecomp, hcimage, ← Scheme.Hom.comp_apply, Category.assoc, ← Over.comp_left]
  obtain ⟨U, hηU, hU⟩ := exists_finite_imageι_comp_morphismRestrict_of_finite_image_preimage
    γ.left (fst G H).left (η[G].left point) (by
      dsimp [-Scheme.Hom.comp_base, γ]
      simp only [pullback.lift_fst]
      exact (Set.finite_singleton _).subset hfinite)
  have hUfinite (x : U) :
      ((pullback.fst G.hom H.hom) ⁻¹' {x.1} ∩ Set.range ⇑γ.left).Finite := by
    refine ((((γ.left.imageι ≫ (fst G H).left) ∣_ U).finite_preimage_singleton x).image
      (Scheme.Opens.ι _ ≫ γ.left.imageι)).subset ?_
    have hx : U.ι ⁻¹' {x.1} = {x} := by ext; simp
    rw [← hx, ← Set.preimage_comp, ← TopCat.coe_comp, ← Scheme.Hom.comp_base,
      morphismRestrict_ι, ← Category.assoc, Scheme.Hom.comp_base (_ ≫ _) (fst G H).left,
      TopCat.coe_comp, Set.preimage_comp, Set.image_preimage_eq_inter_range]
    simp only [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, Scheme.Opens.range_ι]
    dsimp
    rw [Set.image_preimage_eq_inter_range, Scheme.IdealSheafData.range_subschemeι,
      Scheme.Hom.support_ker, ← Set.inter_assoc, ← Set.preimage_inter,
      Set.singleton_inter_of_mem x.2, IsClosed.closure_eq
      (by exact γ.left.isClosedMap.isClosed_range)]
  refine ext_of_apply_eq H.hom _
    ((fst G G).left ⁻¹ᵁ U).isOpen.isLocallyClosed
    (((fst G G).left ⁻¹ᵁ U).isOpen.dense ?_) ?_ ?_
  · exact .preimage ⟨_, hηU⟩ (fst G G).left.surjective
  · intro y hyU hy
    have hx : IsClosed {(fst G G).left y} := by
      simpa using (fst G G).left.isClosedMap _ hy
    let x : 𝟙_ _ ⟶ G := Over.homMk (pointOfClosedPoint G.hom _ hx) (by simp)
    let xe : (G ⊗ G).left := (fst G G ≫ (ρ_ _).inv ≫ G ◁ η[G]).left y
    let target : (G ⊗ H).left := (fst G G ≫ (ρ_ _).inv ≫ G ◁ η[H]).left y
    have heq : γ.left y = target := by
      refine subsingleton_image_closure_of_finite_of_isPreirreducible
        (hx.preimage (fst G G).left.continuous).isLocallyClosed ?_ γ.left.continuous
        γ.left.isClosedMap ((hUfinite ⟨_, hyU⟩).subset (Set.image_subset_iff.mpr fun _ ↦ by
          simp [← Scheme.Hom.comp_apply, -Scheme.Hom.comp_base, γ])) ?_ ?_
      · let α : G ⊗ G ⟶ G ⊗ G := toUnit _ ≫ x ⊗ₘ 𝟙 _
        convert!
          ((IrreducibleSpace.isIrreducible_univ _).image α.left
              α.left.continuous.continuousOn).isPreirreducible
        rw [Over.tensorHom_left]
        simp [Set.range_comp, Scheme.Pullback.range_map, x]
      · exact ⟨y, subset_closure (by simp), rfl⟩
      · refine ⟨xe, subset_closure ?_, ?_⟩
        · simp [xe, ← Scheme.Hom.comp_apply, -Scheme.Hom.comp_base]
        · simp only [xe, target, ← Scheme.Hom.comp_apply, ← Over.comp_left]
          simp [Category.assoc, γ_right]
    convert! congr((snd G H).left $heq) using 1
    · simp [γ, ← Scheme.Hom.comp_apply]
    · simp [target, Hom.one_def, ← Scheme.Hom.comp_apply, -Scheme.Hom.comp_base]
  · simp

/-- A pointed morphism of proper group schemes is a group homomorphism when
the source product is integral. -/
theorem isMonHom_of_pointed_of_integral_product
    {K : Type u} [Field K] [IsAlgClosed K]
    (G H : Over (Spec (.of K))) [IsProper G.hom] [IsProper H.hom]
    [IsIntegral (G ⊗ G).left] [GrpObj G] [GrpObj H]
    (f : G ⟶ H) (hf : η[G] ≫ f = η[H]) : IsMonHom f := by
  let d : G ⊗ G ⟶ H :=
    (μ[G] ≫ f) / ((fst G G ≫ f) * (snd G G ≫ f))
  have hμl : η[G] ▷ G ≫ μ[G] = (λ_ G).hom := by
    simpa only [tensorHom_id] using MonObj.one_mul G
  have hμr : G ◁ η[G] ≫ μ[G] = (ρ_ G).hom := by
    simpa only [id_tensorHom] using MonObj.mul_one G
  have hl : η[G] ▷ G ≫ d = 1 := by
    dsimp [d]
    rw [GrpObj.comp_div, comp_mul]
    simp only [← Category.assoc, hμl, whiskerRight_fst, whiskerRight_snd]
    rw [Category.assoc, hf]
    simp [leftUnitor_hom, one_eq_one]
  have hr : G ◁ η[G] ≫ d = 1 := by
    dsimp [d]
    rw [GrpObj.comp_div, comp_mul]
    simp only [← Category.assoc, hμr, whiskerLeft_fst, whiskerLeft_snd]
    rw [Category.assoc, hf]
    simp [rightUnitor_hom, one_eq_one]
  have hd := rigidity_eq_one G H d hl hr
  refine ⟨hf, ?_⟩
  have hmul : μ[G] ≫ f = (fst G G ≫ f) * (snd G G ≫ f) := div_eq_one.mp hd
  simpa only [Hom.mul_def, ← lift_map, lift_fst_snd, Category.id_comp] using hmul

end

end OAI.AlgebraicGeometry.Albanese.Construction.Rigidity
