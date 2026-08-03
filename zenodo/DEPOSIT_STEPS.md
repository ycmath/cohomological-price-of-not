# Zenodo deposit (owner manual steps)

1. zenodo.org 로그인 → GitHub 연동 (Settings → GitHub) 에서
   `ycmath/cohomological-price-of-not` 토글 ON.
2. GitHub에서 release `v1.0.0` 생성 → Zenodo가 자동 아카이브 + DOI 발급.
   (또는 수동 업로드: repo zip + `metadata.json` 내용 입력.)
3. 발급된 **concept DOI** 를 README 상단 배지로 추가:
   `[![DOI](https://zenodo.org/badge/DOI/<doi>.svg)](https://doi.org/<doi>)`
   그리고 "Zenodo DOI: to be added upon deposit" 문구 교체.
4. CITATION.cff 에 `doi:` 필드 추가 후 커밋.

(선례: inversion-wilf-spi — concept DOI 10.5281/zenodo.21474657 형식.)
