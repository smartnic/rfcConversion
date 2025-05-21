document.addEventListener('DOMContentLoaded', function() {
    // DOM elements
    const converterForm = document.getElementById('converter-form');
    const rfcTextInput = document.getElementById('rfc-text');
    const outputFormatSelect = document.getElementById('output-format');
    const modelSelect = document.getElementById('model-select');
    const convertBtn = document.getElementById('convert-btn');
    const spinner = document.getElementById('spinner');
    const resultsContainer = document.getElementById('results-container');
    const resultOutput = document.getElementById('result-output');
    const copyResultBtn = document.getElementById('copy-result');
    const explanationSection = document.getElementById('explanation-section');
    const explanationContent = document.getElementById('explanation-content');
    const visualizationSection = document.getElementById('visualization-section');
    const visualizationContainer = document.getElementById('visualization-container');
    const exampleItems = document.querySelectorAll('.example-item');

    // Fetch available models
    fetchAvailableModels();

    // Event listeners
    converterForm.addEventListener('submit', handleFormSubmit);
    copyResultBtn.addEventListener('click', copyResultToClipboard);
    outputFormatSelect.addEventListener('change', handleFormatChange);
    exampleItems.forEach(item => {
        item.addEventListener('click', handleExampleClick);
    });

    // Functions
    function fetchAvailableModels() {
        fetch('/available_models')
            .then(response => response.json())
            .then(data => {
                // Clear existing options
                modelSelect.innerHTML = '';
                
                // Add options for each model
                data.models.forEach(model => {
                    const option = document.createElement('option');
                    option.value = model;
                    option.textContent = model.split('/').pop(); // Just show the model name, not the full path
                    modelSelect.appendChild(option);
                });
                
                // Select the default model
                modelSelect.value = 'mistralai/Mixtral-8x7B-Instruct-v0.1';
            })
            .catch(error => {
                console.error('Error fetching models:', error);
            });
    }

    function handleFormSubmit(event) {
        event.preventDefault();
        
        const rfcText = rfcTextInput.value.trim();
        if (!rfcText) {
            alert('Please enter an RFC rule to convert.');
            return;
        }
        
        // Show loading state
        convertBtn.disabled = true;
        spinner.classList.remove('d-none');
        
        // Prepare request data
        const requestData = {
            rfc_text: rfcText,
            output_format: outputFormatSelect.value,
            model: modelSelect.value
        };
        
        // Send request to server
        fetch('/convert', {
            method: 'POST',
            headers: {
                'Content-Type': 'application/json'
            },
            body: JSON.stringify(requestData)
        })
        .then(response => response.json())
        .then(data => {
            // Hide loading state
            convertBtn.disabled = false;
            spinner.classList.add('d-none');
            
            if (data.success) {
                displayResults(data);
            } else {
                alert('Error: ' + data.error);
            }
        })
        .catch(error => {
            // Hide loading state
            convertBtn.disabled = false;
            spinner.classList.add('d-none');
            alert('An error occurred: ' + error.message);
        });
    }

    function displayResults(data) {
        // Show results container
        resultsContainer.style.display = 'block';
        
        // Update result output
        resultOutput.textContent = data.result;
        
        // Update language class for syntax highlighting
        if (data.format === 'FOL') {
            resultOutput.className = 'language-none';
            
            // Show explanation section
            explanationSection.style.display = 'block';
            
            // Update explanation content
            if (data.explanation && Object.keys(data.explanation).length > 0) {
                let explanationHtml = `
                    <div class="row">
                        <div class="col-md-6">
                            <h6>Conditions:</h6>
                            <p>${data.explanation.conditions || 'Not available'}</p>
                        </div>
                        <div class="col-md-6">
                            <h6>Actions:</h6>
                            <p>${data.explanation.actions || 'Not available'}</p>
                        </div>
                    </div>
                `;
                
                if (data.explanation.variables && data.explanation.variables.length > 0) {
                    explanationHtml += `
                        <div class="row mt-2">
                            <div class="col-12">
                                <h6>Variables:</h6>
                                <p>${data.explanation.variables.map(v => `<span class="badge bg-secondary me-1">${v}</span>`).join(' ')}</p>
                            </div>
                        </div>
                    `;
                }
                
                explanationContent.innerHTML = explanationHtml;
            } else {
                explanationContent.innerHTML = '<p>No explanation available for this formula.</p>';
            }
            
            // Show visualization section and create visualization
            visualizationSection.style.display = 'block';
            createVisualization(data.result);
        } else {
            // For SMT-LIB, use different syntax highlighting
            resultOutput.className = 'language-lisp';
            
            // Hide explanation and visualization sections
            explanationSection.style.display = 'none';
            visualizationSection.style.display = 'none';
        }
        
        // Apply syntax highlighting
        Prism.highlightElement(resultOutput);
        
        // Scroll to results
        resultsContainer.scrollIntoView({ behavior: 'smooth' });
    }

    function createVisualization(folFormula) {
        // Clear previous visualization
        visualizationContainer.innerHTML = '';
        
        try {
            // Parse FOL formula into a graph structure
            const graph = parseFOLToGraph(folFormula);
            
            // Create D3.js visualization
            const width = visualizationContainer.clientWidth;
            const height = visualizationContainer.clientHeight;
            
            const svg = d3.select('#visualization-container')
                .append('svg')
                .attr('width', width)
                .attr('height', height);
            
            // Create a force simulation
            const simulation = d3.forceSimulation(graph.nodes)
                .force('link', d3.forceLink(graph.links).id(d => d.id).distance(100))
                .force('charge', d3.forceManyBody().strength(-300))
                .force('center', d3.forceCenter(width / 2, height / 2));
            
            // Add links
            const link = svg.append('g')
                .attr('class', 'links')
                .selectAll('line')
                .data(graph.links)
                .enter()
                .append('line')
                .attr('class', 'link')
                .attr('stroke-width', d => d.value);
            
            // Add nodes
            const node = svg.append('g')
                .attr('class', 'nodes')
                .selectAll('.node')
                .data(graph.nodes)
                .enter()
                .append('g')
                .attr('class', 'node')
                .call(d3.drag()
                    .on('start', dragstarted)
                    .on('drag', dragged)
                    .on('end', dragended));
            
            // Add circles to nodes
            node.append('circle')
                .attr('r', d => d.type === 'operator' ? 15 : 10)
                .attr('fill', d => getNodeColor(d));
            
            // Add text to nodes
            node.append('text')
                .attr('dy', 4)
                .attr('text-anchor', 'middle')
                .text(d => d.label)
                .attr('fill', d => d.type === 'operator' ? 'white' : 'black');
            
            // Update positions on each tick
            simulation.on('tick', () => {
                link
                    .attr('x1', d => d.source.x)
                    .attr('y1', d => d.source.y)
                    .attr('x2', d => d.target.x)
                    .attr('y2', d => d.target.y);
                
                node.attr('transform', d => `translate(${d.x},${d.y})`);
            });
            
            // Drag functions
            function dragstarted(event, d) {
                if (!event.active) simulation.alphaTarget(0.3).restart();
                d.fx = d.x;
                d.fy = d.y;
            }
            
            function dragged(event, d) {
                d.fx = event.x;
                d.fy = event.y;
            }
            
            function dragended(event, d) {
                if (!event.active) simulation.alphaTarget(0);
                d.fx = null;
                d.fy = null;
            }
        } catch (error) {
            visualizationContainer.innerHTML = `
                <div class="alert alert-warning">
                    Unable to visualize this formula: ${error.message}
                </div>
            `;
        }
    }

    function parseFOLToGraph(folFormula) {
        // This is a simplified parser for demonstration
        // A complete parser would need to handle the full FOL grammar
        
        // Basic parsing to identify main components
        const nodes = [];
        const links = [];
        let nodeId = 0;
        
        // Add the root node (universal or existential quantifier)
        if (folFormula.startsWith('∀') || folFormula.startsWith('∃')) {
            const quantifier = folFormula.startsWith('∀') ? '∀' : '∃';
            const rootNode = {
                id: nodeId++,
                label: quantifier,
                type: 'operator'
            };
            nodes.push(rootNode);
            
            // Find the main variables
            const variables = [];
            let varSection = folFormula.substring(1, folFormula.indexOf('('));
            for (let i = 0; i < varSection.length; i++) {
                if (/[a-z]/.test(varSection[i])) {
                    variables.push(varSection[i]);
                }
            }
            
            // Add variable nodes
            variables.forEach(variable => {
                const varNode = {
                    id: nodeId++,
                    label: variable,
                    type: 'variable'
                };
                nodes.push(varNode);
                links.push({
                    source: rootNode.id,
                    target: varNode.id,
                    value: 1
                });
            });
            
            // Add implication operator if present
            if (folFormula.includes('→')) {
                const implNode = {
                    id: nodeId++,
                    label: '→',
                    type: 'operator'
                };
                nodes.push(implNode);
                links.push({
                    source: rootNode.id,
                    target: implNode.id,
                    value: 2
                });
                
                // Split into conditions and actions
                const parts = folFormula.split('→');
                
                // Add a simplified condition node
                const condNode = {
                    id: nodeId++,
                    label: 'Conditions',
                    type: 'group'
                };
                nodes.push(condNode);
                links.push({
                    source: implNode.id,
                    target: condNode.id,
                    value: 1
                });
                
                // Add a simplified action node
                const actionNode = {
                    id: nodeId++,
                    label: 'Actions',
                    type: 'group'
                };
                nodes.push(actionNode);
                links.push({
                    source: implNode.id,
                    target: actionNode.id,
                    value: 1
                });
                
                // Extract predicates from conditions
                const condText = parts[0];
                const condPredicates = extractPredicates(condText);
                condPredicates.forEach(pred => {
                    const predNode = {
                        id: nodeId++,
                        label: pred,
                        type: 'predicate'
                    };
                    nodes.push(predNode);
                    links.push({
                        source: condNode.id,
                        target: predNode.id,
                        value: 1
                    });
                });
                
                // Extract predicates from actions
                const actionText = parts[1];
                const actionPredicates = extractPredicates(actionText);
                actionPredicates.forEach(pred => {
                    const predNode = {
                        id: nodeId++,
                        label: pred,
                        type: 'predicate'
                    };
                    nodes.push(predNode);
                    links.push({
                        source: actionNode.id,
                        target: predNode.id,
                        value: 1
                    });
                });
            }
        }
        
        return { nodes, links };
    }

    function extractPredicates(text) {
        // Very simplified predicate extractor
        // Extract capital-letter-starting words that might be predicates
        const predicates = [];
        const matches = text.match(/[A-Z][a-zA-Z]*\([^)]*\)/g) || [];
        
        matches.forEach(match => {
            predicates.push(match.split('(')[0]);
        });
        
        return [...new Set(predicates)]; // Remove duplicates
    }

    function getNodeColor(node) {
        switch (node.type) {
            case 'operator':
                return '#3388dd';
            case 'variable':
                return '#44bb99';
            case 'predicate':
                return '#ffaa44';
            case 'group':
                return '#ee6677';
            default:
                return '#aaaaaa';
        }
    }

    function copyResultToClipboard() {
        navigator.clipboard.writeText(resultOutput.textContent)
            .then(() => {
                // Show success message
                const originalText = copyResultBtn.innerHTML;
                copyResultBtn.innerHTML = '<i class="fas fa-check"></i> Copied!';
                setTimeout(() => {
                    copyResultBtn.innerHTML = originalText;
                }, 2000);
            })
            .catch(err => {
                console.error('Failed to copy: ', err);
            });
    }

    function handleFormatChange() {
        // Update UI based on selected format
        if (outputFormatSelect.value === 'FOL') {
            // Nothing to do here
        } else {
            // Clear any existing results
            if (resultsContainer.style.display !== 'none') {
                resultsContainer.style.display = 'none';
            }
        }
    }

    function handleExampleClick(event) {
        // Fill the input with the example text
        rfcTextInput.value = event.target.textContent.trim();
        rfcTextInput.focus();
    }
}); 