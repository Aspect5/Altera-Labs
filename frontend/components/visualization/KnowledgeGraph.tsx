import React, { useEffect, useRef } from 'react';
import * as d3 from 'd3';
import { D3Node, D3Link } from '../../types';
import { KnowledgeState, GraphNode, Edge } from '../../types/components';

interface KnowledgeGraphProps {
    nodes: GraphNode[];
    edges: Edge[];
    knowledgeState: KnowledgeState;
}

const getMasteryColor = (mu: number): string => {
    if (mu > 0.8) return '#22c55e'; // green-500
    if (mu > 0.4) return '#facc15'; // yellow-400
    if (mu > 0.0) return '#ef4444'; // red-500
    return '#6b7280'; // gray-500
};

const KnowledgeGraph: React.FC<KnowledgeGraphProps> = ({ nodes, edges, knowledgeState }) => {
    const ref = useRef<SVGSVGElement>(null);
    const containerRef = useRef<HTMLDivElement>(null);
    const nodePositions = useRef(new Map<string, { x: number, y: number, vx: number, vy: number }>());

    // Effect to clear positions only when the graph structure changes
    useEffect(() => {
        nodePositions.current.clear();
    }, [nodes, edges]);

    // Main rendering effect
    useEffect(() => {
        if (!ref.current || !containerRef.current || nodes.length === 0) return;

        const container = containerRef.current;
        const width = container.clientWidth;
        const height = container.clientHeight;

        const d3Nodes: D3Node[] = nodes.map(node => {
            const savedPos = nodePositions.current.get(node.id);
            return {
                ...node,
                mu: knowledgeState[node.id]?.mu || 0,
                sigma: knowledgeState[node.id]?.sigma || 0,
                ...(savedPos && { x: savedPos.x, y: savedPos.y, vx: savedPos.vx, vy: savedPos.vy }),
            };
        });

        const d3Links: D3Link[] = edges.map(edge => ({
            ...edge,
            source: edge.source,
            target: edge.target,
        }));

        const svg = d3.select(ref.current)
            .attr('width', width)
            .attr('height', height)
            .attr('viewBox', [-width / 2, -height / 2, width, height]);

        const zoom = d3.zoom<SVGSVGElement, unknown>()
            .on("zoom", (event: d3.D3ZoomEvent<SVGSVGElement, unknown>) => {
                g.attr("transform", event.transform.toString());
            });

        svg.call(zoom);

        svg.selectAll("*").remove(); // Clear previous render
        const g = svg.append("g");
        
        const defs = svg.append('defs');
        const filter = defs.append('filter')
            .attr('id', 'glow');
        filter.append('feGaussianBlur')
            .attr('stdDeviation', '3.5')
            .attr('result', 'coloredBlur');
        const feMerge = filter.append('feMerge');
        feMerge.append('feMergeNode').attr('in', 'coloredBlur');
        feMerge.append('feMergeNode').attr('in', 'SourceGraphic');

        const simulation = d3.forceSimulation<D3Node, D3Link>(d3Nodes)
            .force('link', d3.forceLink<D3Node, D3Link>(d3Links).id(d => d.id).distance(150))
            .force('charge', d3.forceManyBody().strength(-450))
            .force('center', d3.forceCenter(0, 0))
            .force('collision', d3.forceCollide().radius(40));

        const link = g.append('g')
            .attr('stroke', '#94a3b8') // slate-400
            .attr('stroke-opacity', 0.6)
            .selectAll('line')
            .data(d3Links)
            .join('line')
            .attr('stroke-width', (d) => Math.max(1, d.weight * 5));
        
        const node = g.append('g')
            .selectAll<SVGGElement, D3Node>('g')
            .data(d3Nodes)
            .join('g')
            .call(drag(simulation));

        // Halo for uncertainty
        node.append('circle')
            .attr('r', 25)
            .attr('fill', (d) => getMasteryColor(d.mu))
            .attr('stroke', (d) => getMasteryColor(d.mu))
            .attr('stroke-width', (d) => d.sigma * 15) // Sigma controls halo width
            .style('filter', 'url(#glow)');

        // Main node circle
        node.append('circle')
            .attr('r', 25)
            .attr('stroke', '#e2e8f0') // slate-200
            .attr('stroke-width', 1.5)
            .attr('fill', (d) => getMasteryColor(d.mu));

        node.append('text')
            .attr('dy', '0.35em')
            .attr('text-anchor', 'middle')
            .attr('fill', (d) => d.mu > 0.8 ? '#000' : '#f8fafc')
            .attr('font-size', '12px')
            .attr('font-weight', 'bold')
            .text((d) => d.label)
            .style('pointer-events', 'none');

        simulation.on('tick', () => {
            link
                .attr('x1', (d) => (d.source as D3Node).x!)
                .attr('y1', (d) => (d.source as D3Node).y!)
                .attr('x2', (d) => (d.target as D3Node).x!)
                .attr('y2', (d) => (d.target as D3Node).y!);

            node
                .attr('transform', (d) => `translate(${d.x},${d.y})`)
                .each(d => {
                    if (d.x !== undefined && d.y !== undefined && d.vx !== undefined && d.vy !== undefined) {
                        nodePositions.current.set(d.id, { x: d.x, y: d.y, vx: d.vx, vy: d.vy });
                    }
                });
        });

        function drag(simulation: d3.Simulation<D3Node, D3Link>): d3.DragBehavior<SVGGElement, D3Node, D3Node> {    
            function dragstarted(event: d3.D3DragEvent<SVGGElement, D3Node, D3Node>) {
              if (!event.active) simulation.alphaTarget(0.3).restart();
              event.subject.fx = event.subject.x;
              event.subject.fy = event.subject.y;
            }
            function dragged(event: d3.D3DragEvent<SVGGElement, D3Node, D3Node>) {
              event.subject.fx = event.x;
              event.subject.fy = event.y;
            }
            function dragended(event: d3.D3DragEvent<SVGGElement, D3Node, D3Node>) {
              if (!event.active) simulation.alphaTarget(0);
              event.subject.fx = null;
              event.subject.fy = null;
            }
            return d3.drag<SVGGElement, D3Node, D3Node>()
                .on("start", dragstarted)
                .on("drag", dragged)
                .on("end", dragended);
        }

        const handleResize = () => {
             const newWidth = container.clientWidth;
             const newHeight = container.clientHeight;
             svg.attr('width', newWidth).attr('height', newHeight);
             svg.attr('viewBox', [-newWidth / 2, -newHeight / 2, newWidth, newHeight]);
             simulation.force('center', d3.forceCenter(0, 0)).restart();
        };

        window.addEventListener('resize', handleResize);

        return () => {
            simulation.stop();
            window.removeEventListener('resize', handleResize);
        };
    }, [knowledgeState, nodes, edges]);

    return (
        <div ref={containerRef} className="w-full h-full">
            <svg ref={ref}></svg>
        </div>
    );
};

export default KnowledgeGraph;