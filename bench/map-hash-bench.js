/*
 * Map key distribution benchmark
 *
 * For each family of keys: build a Map of N entries, check that every key
 * round-trips, then time looking every key up once. Hash buckets cannot be
 * observed from JavaScript, so the signal is how the cost of one lookup
 * changes with N: about flat when the keys are spread over the buckets,
 * growing with N when they pile up in a few of them.
 *
 * Runs unmodified under qjs, node and d8:
 *
 *   qjs bench/map-hash-bench.js [sizes]
 *
 * where sizes is a comma separated list, 1000,10000,100000 by default.
 */
"use strict";

var log = typeof console !== "undefined" ? function(s) { console.log(s); } : print;

var now = typeof performance !== "undefined" ?
    function() { return performance.now(); } : Date.now;

var argv = typeof scriptArgs !== "undefined" ? scriptArgs.slice(1) :
    typeof process !== "undefined" ? process.argv.slice(2) :
    typeof arguments !== "undefined" ? Array.prototype.slice.call(arguments) : [];

var sizes = (argv[0] || "1000,10000,100000").split(",").map(Number);

/* a timed batch of passes lasts at least this long */
var MIN_BATCH_MS = 5;
/* stop when this many batches in a row did not improve the minimum by 1% */
var STABLE_BATCHES = 8;
/* or when a cell has been timed for this long (at least two batches) */
var BUDGET_MS = 500;

function engine_name()
{
    if (typeof process !== "undefined" && process.versions && process.versions.v8)
        return "node " + process.version + " (V8 " + process.versions.v8 + ")";
    if (typeof version === "function")
        return "d8 (V8 " + version() + ")";
    return "qjs";
}

function assert(cond, msg)
{
    if (!cond)
        throw new Error("assertion failed: " + msg);
}

/* A fixed bijection on [0, 2^31): distinct i give distinct, scattered ids.
   Every step (add, multiply by an odd constant, xor-shift) is invertible
   modulo 2^31. */
function scramble31(i)
{
    var x = (i + 0x1234567) & 0x7fffffff;
    x = Math.imul(x, 0x9e3779b1) & 0x7fffffff;
    x ^= x >>> 15;
    x = Math.imul(x, 0x85ebca6b) & 0x7fffffff;
    x ^= x >>> 13;
    x = Math.imul(x, 0xc2b2ae35) & 0x7fffffff;
    x ^= x >>> 16;
    return x;
}

var families = [
    /* integers */
    [ "i (consecutive ids)", function(i) { return i; } ],
    [ "i * 2^3",             function(i) { return i * 8; } ],
    [ "i * 2^10",            function(i) { return i * 1024; } ],
    [ "i * 2^16",            function(i) { return i * 65536; } ],
    [ "i * 2^20",            function(i) { return i * 1048576; } ],
    [ "i * 7919",            function(i) { return i * 7919; } ],
    [ "random < 2^31",       scramble31 ],
    [ "-1 - i",              function(i) { return -1 - i; } ],
    /* integers that do not fit in 32 bits; above 2^53 only the even ones
       are representable, hence the step of 2 */
    [ "2^32 + i",            function(i) { return 4294967296 + i; } ],
    /* what Date.now() returns, one millisecond apart */
    [ "1.7e12 + i (time, ms)", function(i) { return 1700000000000 + i; } ],
    [ "2^53 + 2i",           function(i) { return 9007199254740992 + 2 * i; } ],
    /* non-integers */
    [ "i + 0.5",             function(i) { return i + 0.5; } ],
    /* identity keys */
    [ "objects",             function(i) { return { id: i }; } ],
    [ "symbols",             function(i) { return Symbol(); } ],
    /* control: hashed by content */
    [ "strings",             function(i) { return "k" + i; } ],
];

function make_keys(make, n)
{
    var keys = [], i;
    for (i = 0; i < n; i++)
        keys.push(make(i));
    return keys;
}

/* build the Map and check that it holds exactly the keys, in order */
function build(keys, n)
{
    var m = new Map(), i, k;
    for (i = 0; i < n; i++)
        m.set(keys[i], i);
    assert(m.size === n, "the keys are distinct");
    for (i = 0; i < n; i++)
        assert(m.has(keys[i]) && m.get(keys[i]) === i, "key round-trips");
    i = 0;
    for (k of m.keys())
        assert(k === keys[i++], "iteration follows insertion order");
    assert(i === n, "iteration visits every key");
    return m;
}

/* look every key up once; the sum of the values proves that all were found */
function lookup_pass(m, keys, n)
{
    var sum = 0, i;
    for (i = 0; i < n; i++)
        sum += m.get(keys[i]);
    return sum;
}

/* the same loop without the lookup, to tell the cost of the loop itself */
function loop_pass(m, keys, n)
{
    var sum = 0, i;
    for (i = 0; i < n; i++) {
        if (keys[i] !== m)
            sum += i;
    }
    return sum;
}

/* ns per key of pass(m, keys, n), as the fastest of several timed batches */
function measure(pass, m, keys, n)
{
    var expected = n * (n - 1) / 2;
    var reps = 1, best = Infinity, stable = 0, spent = 0, batches = 0;
    var t, dt, r;

    while (batches < 2 || (stable < STABLE_BATCHES && spent < BUDGET_MS)) {
        t = now();
        for (r = 0; r < reps; r++)
            assert(pass(m, keys, n) === expected, "every lookup hits");
        dt = now() - t;
        if (dt < MIN_BATCH_MS) {
            /* too short to time: batch more passes (this also warms up) */
            reps *= 2;
            continue;
        }
        spent += dt;
        batches++;
        dt /= reps;
        stable = dt < best * 0.99 ? 0 : stable + 1;
        if (dt < best)
            best = dt;
    }
    return best * 1e6 / n;
}

/* SameValueZero corner cases that a hash function must not break */
function check_semantics()
{
    var m = new Map([[0, "zero"], [NaN, "nan"], [1, "one"],
                     [2147483648, "2^31"], [0.5, "half"]]);
    var s = new Set([-0, NaN, 1.5 - 0.5]);

    assert(m.size === 5, "map size");
    assert(m.get(-0) === "zero" && m.get(0 * -1) === "zero", "-0 is +0");
    assert(m.get(0 / 0) === "nan" && m.get(-NaN) === "nan", "NaN is NaN");
    assert(m.get(3 - 2) === "one" && m.get(0.5 + 0.5) === "one", "1 is 1.0");
    assert(m.get(1073741824 * 2) === "2^31", "2^31 as a product");
    assert(m.get(4294967296 / 2) === "2^31", "2^31 as a quotient");
    assert(m.get(1 / 2) === "half", "0.5");
    assert(m.get(2) === undefined && !m.has(-1), "misses");
    assert(s.size === 3 && s.has(0) && s.has(NaN) && s.has(1), "set");
    assert(1 / s.values().next().value === Infinity, "-0 is stored as +0");
}

/* Run both passes over every kind of key before timing anything, so that a
   JIT sees the same mix of key types whatever the order of the families. */
function warm_up()
{
    var n = 256, f, keys, m, r;
    for (f = 0; f < families.length; f++) {
        keys = make_keys(families[f][1], n);
        m = build(keys, n);
        for (r = 0; r < 1000; r++) {
            lookup_pass(m, keys, n);
            loop_pass(m, keys, n);
        }
    }
}

function pad(s, n)
{
    s = String(s);
    while (s.length < n)
        s += " ";
    return s;
}

function pad_left(s, n)
{
    s = String(s);
    while (s.length < n)
        s = " " + s;
    return s;
}

function main()
{
    var result = { engine: engine_name(), sizes: sizes, ns: {} };
    var rows = [[ "(loop only, no lookup)", null ]].concat(families);
    var f, j, n, name, keys, m, ns, line;

    check_semantics();
    warm_up();

    log("engine: " + result.engine);
    log("ns per lookup, fastest batch; x = ns at the largest N / ns at the smallest");
    line = pad("key family", 24);
    for (j = 0; j < sizes.length; j++)
        line += pad_left("N=" + sizes[j], 12);
    log(line + pad_left("x", 9));

    for (f = 0; f < rows.length; f++) {
        name = rows[f][0];
        ns = [];
        for (j = 0; j < sizes.length; j++) {
            n = sizes[j];
            if (rows[f][1]) {
                keys = make_keys(rows[f][1], n);
                m = build(keys, n);
                ns.push(measure(lookup_pass, m, keys, n));
            } else {
                keys = make_keys(families[0][1], n);
                ns.push(measure(loop_pass, null, keys, n));
            }
        }
        result.ns[name] = ns.map(function(x) { return Math.round(x * 100) / 100; });
        line = pad(name, 24);
        for (j = 0; j < ns.length; j++)
            line += pad_left(ns[j].toFixed(1), 12);
        log(line + pad_left((ns[ns.length - 1] / ns[0]).toFixed(1), 9));
    }
    log("JSON " + JSON.stringify(result));
}

main();
