// Flutter twin of samples/ui/threads (Koka lib/ui): an fps meter that reads 0
// until something animates, a bouncing bar (20<->240, 500ms easeInOut,
// retargeting at each end), an Animate/Stop button, and a Compute button that
// runs fib(38) off the UI thread (Isolate.run) -- the same demo, same
// renderer (Impeller), different framework. Dark background #16161e like the
// Koka default dark theme.
import 'dart:isolate';
import 'package:flutter/material.dart';
import 'package:flutter/scheduler.dart';

int fib(int n) => n < 2 ? n : fib(n - 1) + fib(n - 2);

void main() => runApp(const BenchApp());

class BenchApp extends StatelessWidget {
  const BenchApp({super.key});
  @override
  Widget build(BuildContext context) => MaterialApp(
        debugShowCheckedModeBanner: false,
        theme: ThemeData.dark(useMaterial3: true),
        home: const BenchPage(),
      );
}

class BenchPage extends StatefulWidget {
  const BenchPage({super.key});
  @override
  State<BenchPage> createState() => _BenchPageState();
}

class _BenchPageState extends State<BenchPage>
    with SingleTickerProviderStateMixin {
  late final AnimationController _bar;   // the bouncing bar
  bool spinning = false;
  bool computing = false;
  int n = 38;
  int? result;

  // fps meter: smoothed 1000/dt over the frames that actually happen
  double _fps = 0.0;
  Duration _last = Duration.zero;
  late final Ticker _meter;

  @override
  void initState() {
    super.initState();
    _bar = AnimationController(
        vsync: this, duration: const Duration(milliseconds: 500));
    _meter = createTicker((now) {
      if (_last != Duration.zero) {
        final dt = (now - _last).inMicroseconds / 1000.0;
        if (dt > 0) {
          final inst = 1000.0 / dt;
          _fps = _fps == 0.0 ? inst : _fps * 0.9 + inst * 0.1;
        }
      }
      _last = now;
      setState(() {});
    });
    const autostart = bool.fromEnvironment('AUTOSTART');
    if (autostart) {
      WidgetsBinding.instance.addPostFrameCallback((_) => _toggleSpin());
    }
  }

  void _toggleSpin() {
    setState(() {
      spinning = !spinning;
      if (spinning) {
        _last = Duration.zero;
        _meter.start();
        _bar.repeat(reverse: true);   // 20 <-> 240 bounce
      } else {
        _meter.stop();
        _fps = 0.0;
        _bar.stop();
        _bar.animateTo(0.0, duration: const Duration(milliseconds: 500));
      }
    });
  }

  Future<void> _compute() async {
    if (computing) return;
    setState(() { computing = true; result = null; });
    final k = n;
    final r = await Isolate.run(() => fib(k));
    setState(() { computing = false; result = r; n = k + 1; });
  }

  @override
  Widget build(BuildContext context) {
    final status = computing
        ? 'computing fib($n) on a worker…'
        : result != null ? 'fib(${n - 1}) = $result' : 'idle';
    return Scaffold(
      backgroundColor: const Color(0xff16161e),
      body: Center(
        child: Card(
          child: Padding(
            padding: const EdgeInsets.all(20),
            child: Column(
              mainAxisSize: MainAxisSize.min,
              children: [
                Text('Koka × threads (Flutter twin)',
                    style: Theme.of(context).textTheme.titleLarge),
                const SizedBox(height: 16),
                Text(spinning ? '${_fps.round()} fps' : 'parked — no frames',
                    style: const TextStyle(
                        fontSize: 40, fontWeight: FontWeight.bold)),
                const SizedBox(height: 16),
                AnimatedBuilder(
                  animation: _bar,
                  builder: (_, __) {
                    final w =
                        20.0 + Curves.easeInOut.transform(_bar.value) * 220.0;
                    return Stack(children: [
                      Container(
                          width: 240, height: 10,
                          decoration: BoxDecoration(
                              color: const Color(0xff23232e),
                              borderRadius: BorderRadius.circular(5))),
                      Container(
                          width: w, height: 10,
                          decoration: BoxDecoration(
                              color: const Color(0xff7aa2f7),
                              borderRadius: BorderRadius.circular(5))),
                    ]);
                  },
                ),
                const SizedBox(height: 16),
                Row(mainAxisSize: MainAxisSize.min, children: [
                  FilledButton(
                      onPressed: _toggleSpin,
                      child: Text(spinning ? 'Stop' : 'Animate')),
                  const SizedBox(width: 8),
                  FilledButton(
                      onPressed: _compute,
                      child: Text(
                          computing ? 'Computing…' : 'Compute fib($n)')),
                ]),
                const SizedBox(height: 16),
                Text(status),
              ],
            ),
          ),
        ),
      ),
    );
  }

  @override
  void dispose() {
    _meter.dispose();
    _bar.dispose();
    super.dispose();
  }
}
