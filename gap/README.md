# The catalogue from GAP

`export_order6_catalogue.g` writes `research/order6/catalogue.json`: for every
class `k = 1, …, 15973` of order six in GAP Smallsemi, the one-based
multiplication table of `SmallSemigroup(6, k)` and whether the semigroup is
self-dual.

```sh
gap -q -c 'OUTPUT_FILE := "catalogue.json";' gap/export_order6_catalogue.g
sha256sum catalogue.json
# 944f356c42b8e703988f5684cd81b650f99cc0ccd1ef1d7fc6e900f2c95f287c with Smallsemi 0.7.2
```

The script is the campaign's export (`gap/export_catalogue_range.g` at the
certified commit) without the guard that restricted it to the campaign's
cluster. The file in this repository is the one produced then: its Git blob id
is the one at the certified commit.

An independent export, made with GAP 4.15.1 and Smallsemi 0.7.2 for the
`bases-min` re-certification (its files `gap/s6_1_10000.json`, SHA-256
`8dbbff19d1dcdcf8ca69414c747aff349ddab9048e574d71a8a200ee1980ea43`, and
`gap/s6_10001_15973.json`, SHA-256
`c453d11c2f9740ce13389fe4e34a8172a7b9fedd586f4e4f0d8860225fefe762`), agrees
with it table for table:

```sh
python3 scripts/check_catalogue.py --gap s6_1_10000.json s6_10001_15973.json
```
