# Export the semigroups of order six from GAP Smallsemi to JSON.
#
#   gap -q -c 'OUTPUT_FILE := "catalogue.json";' gap/export_order6_catalogue.g
#
# writes, for every class i = 1, ..., NrSmallSemigroups(6), the one-based
# multiplication table of SmallSemigroup(6, i) and whether it is self-dual.
# This is the export of the campaign (gap/export_catalogue_range.g at the
# certified commit) without its cluster-allocation guard; with Smallsemi 0.7.2
# it reproduces research/order6/catalogue.json.

if LoadPackage("smallsemi") <> true then
    Error("the GAP Smallsemi package is required");
fi;

SizeScreen([1000000, 1000000]);

if not IsBound(OUTPUT_FILE) then
    OUTPUT_FILE := "research/order6/catalogue.json";
fi;
MIN_ORDER := 6;
MAX_ORDER := 6;

JsonBool := function(value)
    if value then
        return "true";
    fi;
    return "false";
end;

JsonTable := function(table)
    return Concatenation(
        "[",
        JoinStringsWithSeparator(
            List(table, row -> Concatenation(
                "[",
                JoinStringsWithSeparator(List(row, String), ","),
                "]"
            )),
            ","
        ),
        "]"
    );
end;

classCounts := [];
selfDualCounts := [];
totalCount := 0;

PrintTo(OUTPUT_FILE, "{\n");
AppendTo(OUTPUT_FILE,
    "  \"source\": {\"package\": \"GAP Smallsemi\", \"version\": \"",
    PackageInfo("smallsemi")[1].Version,
    "\", \"classification\": \"isomorphism-or-anti-isomorphism\", ",
    "\"oeis\": \"A001423\"},\n");
AppendTo(
    OUTPUT_FILE,
    "  \"scope\": {\"minimum_order\": ",
    MIN_ORDER,
    ", \"maximum_order\": ",
    MAX_ORDER,
    "},\n"
);
AppendTo(OUTPUT_FILE, "  \"semigroups\": [\n");

first := true;
for n in [MIN_ORDER .. MAX_ORDER] do
    classCounts[n] := NrSmallSemigroups(n);
    selfDualCounts[n] := 0;
    totalCount := totalCount + classCounts[n];
    for i in [1 .. classCounts[n]] do
        s := SmallSemigroup(n, i);
        table := MultiplicationTable(s);
        selfdual := IsSelfDualSemigroup(s);
        if selfdual then
            selfDualCounts[n] := selfDualCounts[n] + 1;
        fi;
        if not first then
            AppendTo(OUTPUT_FILE, ",\n");
        fi;
        first := false;
        AppendTo(OUTPUT_FILE,
            "    {\"id\": \"S", n, "_", i,
            "\", \"anti_isomorphism_class_id\": [",
            n, ",", i, "], \"smallsemi_id\": [", n, ",", i,
            "], \"self_dual\": ",
            JsonBool(selfdual), ", \"table\": ", JsonTable(table), "}");
    od;
od;

AppendTo(OUTPUT_FILE, "\n  ],\n");
AppendTo(OUTPUT_FILE, "  \"counts\": {\"anti_isomorphism_classes\": {");
first := true;
for n in [MIN_ORDER .. MAX_ORDER] do
    if not first then
        AppendTo(OUTPUT_FILE, ", ");
    fi;
    first := false;
    AppendTo(OUTPUT_FILE, "\"", n, "\": ", classCounts[n]);
od;
AppendTo(OUTPUT_FILE, "}, \"self_dual\": {");
first := true;
for n in [MIN_ORDER .. MAX_ORDER] do
    if not first then
        AppendTo(OUTPUT_FILE, ", ");
    fi;
    first := false;
    AppendTo(OUTPUT_FILE, "\"", n, "\": ", selfDualCounts[n]);
od;
AppendTo(OUTPUT_FILE, "}, \"total_in_scope\": ", totalCount, "}\n");
AppendTo(OUTPUT_FILE, "}\n");
QUIT_GAP(0);
